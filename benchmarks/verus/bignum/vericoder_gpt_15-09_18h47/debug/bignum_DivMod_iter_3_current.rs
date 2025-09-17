
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
/* helper modified by LLM (iteration 3): build bitstring from nat (MSB at end) */
spec fn NatToBits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        NatToBits(q).push(if r == 1 { '1' } else { '0' })
    }
}

/* helper modified by LLM (iteration 3): Str2Int over push of a single bit */
proof fn lemma_push_properties(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s),
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1,
{}

/* helper modified by LLM (iteration 3): bit-character predicate */
spec fn char_is_bit(c: char) -> bool { c == '0' || c == '1' }

/* helper modified by LLM (iteration 3): pushing a valid bit preserves ValidBitString */
proof fn lemma_valid_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        char_is_bit(c),
    ensures
        ValidBitString(s.push(c)),
{}

/* helper modified by LLM (iteration 3): correctness of NatToBits w.r.t. Str2Int */
proof fn lemma_nat_to_bits_correct(n: nat)
    ensures
        ValidBitString(NatToBits(n)),
        Str2Int(NatToBits(n)) == n,
    decreases n
{
    if n == 0 {
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_nat_to_bits_correct(q);
        lemma_push_properties(NatToBits(q));
    }
}

/* helper modified by LLM (iteration 3): exec constructor producing Vec with correct value */
exec fn nat_to_bits_vec(n: nat) -> (result: Vec<char>)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n,
    decreases n
{
    if n == 0 {
        let v: Vec<char> = Vec::new();
        proof {
            // Str2Int of empty sequence is 0 by definition
        }
        v
    } else {
        let q = n / 2;
        let r = n % 2;
        let mut v = nat_to_bits_vec(q);
        let bit = if r == 1 { '1' } else { '0' };
        let ghost s_old = v@;
        proof {
            assert(ValidBitString(s_old));
            assert(Str2Int(s_old) == q);
        }
        v.push(bit);
        proof {
            if r == 1 { assert(bit == '1'); } else { assert(bit == '0'); }
            lemma_valid_push(s_old, bit);
            assert(v@ == s_old.push(bit));
            lemma_push_properties(s_old);
            if r == 1 {
                assert(v@ == s_old.push('1'));
                assert(Str2Int(v@) == 2 * Str2Int(s_old) + 1);
            } else {
                assert(v@ == s_old.push('0'));
                assert(Str2Int(v@) == 2 * Str2Int(s_old));
            }
            assert(Str2Int(s_old) == q);
            if r == 1 {
                assert(Str2Int(v@) == 2 * q + 1);
            } else {
                assert(Str2Int(v@) == 2 * q + 0);
            }
            assert(n == 2 * q + r);
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): construct quotient and remainder via nat_to_bits_vec */
    let qn = Str2Int(dividend@) / Str2Int(divisor@);
    let rn = Str2Int(dividend@) % Str2Int(divisor@);
    let q = nat_to_bits_vec(qn);
    let r = nat_to_bits_vec(rn);
    (q, r)
}
// </vc-code>

fn main() {}
}


