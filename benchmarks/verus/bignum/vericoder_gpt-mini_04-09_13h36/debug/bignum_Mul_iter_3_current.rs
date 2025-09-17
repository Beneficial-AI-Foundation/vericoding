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
    decreases s.len()
{
    if s.len() == 0 {
        return 0;
    } else {
        let k = s.len();
        let last = s[k - 1];
        let bit: nat = if last == '1' { 1 } else { 0 };
        let prefix = seq_to_nat(&s[0..k - 1]);
        return prefix * 2 + bit;
    }
}

exec fn nat_to_seq(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == old(n)
    decreases n
{
    if n == 0 {
        return Vec::new();
    } else {
        // recursive call for n/2
        let mut rec = nat_to_seq(n / 2);
        // capture the sequence before pushing
        let old_seq: Seq<char> = rec@;
        assert(Str2Int(old_seq) == n / 2);
        let b = if n % 2 == 1 { '1' } else { '0' };
        rec.push(b);
        proof {
            let new_seq: Seq<char> = rec@;
            let len = new_seq.len();
            // new_seq is old_seq with one element appended
            assert(len as int - 1 >= 0);
            assert(new_seq.subrange(0, len as int - 1) == old_seq);
            // by definition of Str2Int on non-empty sequence:
            assert(Str2Int(new_seq) == 2 * Str2Int(new_seq.subrange(0, len as int - 1)) + (if new_seq.index(len as int - 1) == '1' { 1 } else { 0 }));
            // substitute old_seq and b
            assert(Str2Int(new_seq) == 2 * Str2Int(old_seq) + (if b == '1' { 1 } else { 0 }));
            // use recursive call result
            assert(Str2Int(new_seq) == 2 * (n / 2) + (if n % 2 == 1 { 1 } else { 0 }));
            assert(Str2Int(new_seq) == n);
        }
        return rec;
    }
}
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