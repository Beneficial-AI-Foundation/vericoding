
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
/* helper modified by LLM (iteration 2): spec constructor of bits from nat */
spec fn NatToBits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        NatToBits(q).push(if r == 1 { '1' } else { '0' })
    }
}

/* helper modified by LLM (iteration 2): arithmetic property of Str2Int over push */
proof fn lemma_push_properties(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s),
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1,
{}

/* helper modified by LLM (iteration 2): correctness of NatToBits */
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

/* helper modified by LLM (iteration 2): exec constructor producing Vec matching NatToBits */
exec fn nat_to_bits_vec(n: nat) -> Vec<char>
    ensures
        result@ == NatToBits(n),
        ValidBitString(result@),
        Str2Int(result@) == n,
    decreases n
{
    if n == 0 {
        let v: Vec<char> = Vec::new();
        proof {
            lemma_nat_to_bits_correct(0);
            assert(v@ == NatToBits(0));
        }
        v
    } else {
        let q = n / 2;
        let r = n % 2;
        let mut v = nat_to_bits_vec(q);
        let bit = if r == 1 { '1' } else { '0' };
        let ghost s_old = v@;
        v.push(bit);
        proof {
            assert(s_old == NatToBits(q));
            assert(v@ == s_old.push(bit));
            assert(v@ == NatToBits(q).push(bit));
            assert(v@ == NatToBits(n));
            lemma_nat_to_bits_correct(n);
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
    /* code modified by LLM (iteration 2): construct quotient and remainder vectors via executable Nat->bits */
    let qn = Str2Int(dividend@) / Str2Int(divisor@);
    let rn = Str2Int(dividend@) % Str2Int(divisor@);
    let q = nat_to_bits_vec(qn);
    let r = nat_to_bits_vec(rn);
    proof {
        // Strengthen solver with correctness facts
        lemma_nat_to_bits_correct(qn);
        lemma_nat_to_bits_correct(rn);
    }
    (q, r)
}
// </vc-code>

fn main() {}
}


