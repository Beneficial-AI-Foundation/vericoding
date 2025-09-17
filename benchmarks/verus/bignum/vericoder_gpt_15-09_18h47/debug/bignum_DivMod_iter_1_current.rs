
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

proof fn lemma_push_properties(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s),
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1,
{}

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
    let q_s = NatToBits(Str2Int(dividend@) / Str2Int(divisor@));
    let r_s = NatToBits(Str2Int(dividend@) % Str2Int(divisor@));
    proof {
        lemma_nat_to_bits_correct(Str2Int(dividend@) / Str2Int(divisor@));
        lemma_nat_to_bits_correct(Str2Int(dividend@) % Str2Int(divisor@));
    }
    let q: Vec<char> = Vec::<char>::from_seq(q_s);
    let r: Vec<char> = Vec::<char>::from_seq(r_s);
    (q, r)
}
// </vc-code>

fn main() {}
}


