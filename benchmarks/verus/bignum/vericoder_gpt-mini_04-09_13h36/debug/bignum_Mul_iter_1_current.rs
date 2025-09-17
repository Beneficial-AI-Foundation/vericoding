use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
// <vc-helpers>

spec fn pow2(k: nat) -> nat
{
    if k == 0 { 1 } else { 2 * pow2(k - 1) }
}

spec fn BitsValueLSB(t: Seq<char>) -> nat
{
    if t.len() == 0 {
        0
    } else {
        (if t.index(0) == '1' { 1 } else { 0 })
          + 2 * BitsValueLSB(t.subrange(1, t.len()))
    }
}

proof fn bits_rev_correct(t: Seq<char>)
    requires ValidBitString(t)
    ensures Str2Int(t.reverse()) == BitsValueLSB(t)
    decreases t.len()
{
    if t.len() == 0 {
        return;
    } else {
        // Inductive hypothesis on tail
        bits_rev_correct(t.subrange(1, t.len()));

        // Let s = reverse(t). Then:
        // Str2Int(s) = 2 * Str2Int(s.subrange(0, s.len()-1)) + lastbit(s)
        // s.subrange(0, s.len()-1) == reverse(t.subrange(1, t.len()))
        // lastbit(s) == t.index(0)
        proof {
            let s = t.reverse();
            let k = s.len();
            assert(k == t.len());
            // s.subrange(0, k-1) is reverse of tail
            assert(s.subrange(0, k as int - 1) == t.subrange(1, t.len()).reverse());
            // by definition of Str2Int:
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, k as int - 1)) + (if s.index(k as int - 1) == '1' { 1 } else { 0 }));
            // last char of s equals first char of t
            assert(s.index(k as int - 1) == t.index(0));
            // apply inductive hypothesis to the reversed tail
            assert(Str2Int(s.subrange(0, k as int - 1)) == BitsValueLSB(t.subrange(1, t.len())));
            // combine equalities
            assert(Str2Int(s) == 2 * BitsValueLSB(t.subrange(1, t.len())) + (if t.index(0) == '1' { 1 } else { 0 }));
            assert(Str2Int(s) == BitsValueLSB(t));
        }
    }
}

exec fn seq_to_nat(s: &[char]) -> (n: nat)
    requires ValidBitString(s@)
    ensures n == Str2Int(s@)
{
    let mut res: nat = 0;
    let mut i: usize = 0;
    while i < s.len() {
        invariant i <= s.len();
        invariant ValidBitString(s@);
        invariant res == Str2Int(s@.subrange(0, i as int));
        {
            let bit = if s[i] == '1' { 1 } else { 0 };
            // By definition of Str2Int on the prefix extended by one char:
            // Str2Int(s.subrange(0, i+1)) = 2 * Str2Int(s.subrange(0, i)) + bit
            res = res * 2 + bit;
            i = i + 1;
        }
    }
    return res;
}

exec fn nat_to_seq(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == old(n)
{
    let orig: nat = n;
    let mut rev: Vec<char> = Vec::new(); // stores bits from LSB to MSB

    // Invariant: orig == n * pow2(rev.len()) + BitsValueLSB(rev@)
    while n > 0 {
        invariant ValidBitString(rev@);
        invariant orig == n * pow2(rev.len() as nat) + BitsValueLSB(rev@);
        {
            let b = if n % 2 == 1 { '1' } else { '0' };
            if n % 2 == 1 {
                rev.push('1');
            } else {
                rev.push('0');
            }
            n = n / 2;
            // After pushing, the invariant holds by simple arithmetic:
            // new_rev_bits = b + 2 * old_bits
            // new_n = old_n / 2
            // orig = old_n * 2^k + old_bits = (new_n) * 2^(k+1) + new_bits
        }
    }

    // At this point n == 0, so orig == BitsValueLSB(rev@)
    // Now reverse rev into res to obtain MSB..LSB ordering
    let mut res_vec: Vec<char> = Vec::new();
    let mut idx: usize = rev.len();
    while idx > 0 {
        invariant idx <= rev.len();
        invariant ValidBitString(res_vec@);
        idx = idx - 1;
        // push rev[idx]
        res_vec.push(rev.index(idx));
    }

    // Now res_vec is reverse(rev), i.e., MSB..LSB representation.
    // By lemma bits_rev_correct: Str2Int(reverse(rev@)) == BitsValueLSB(rev@)
    proof {
        // use lemma on rev@
        assert(ValidBitString(rev@));
        bits_rev_correct(rev@);
        assert(Str2Int(rev@.reverse()) == BitsValueLSB(rev@));
        // rev@.reverse() corresponds to res_vec@
        assert(res_vec@ == rev@.reverse());
        assert(Str2Int(res_vec@) == BitsValueLSB(rev@));
        assert(Str2Int(res_vec@) == orig);
    }

    return res_vec;
}

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = seq_to_nat(s1);
    let n2 = seq_to_nat(s2);
    let prod = n1 * n2;
    let r = nat_to_seq(prod);
    return r;
}
// </vc-code>

fn main() {}
}