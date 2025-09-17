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
/* helper modified by LLM (iteration 5): added function to_bit_seq */
spec fn to_bit_seq(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    seq!['0']
  } else if n == 1 {
    seq!['1']
  } else {
    let remainder = n % 2;
    let quotient = n / 2;
    let mut result = to_bit_seq(quotient);
    result.push(if remainder == 1 { '1' } else { '0' });
    result
  }
}

proof fn lemma_Str2Int_to_bit_seq(n: nat)
    ensures Str2Int(to_bit_seq(n)) == n
    decreases n
{
    if n > 1 {
        let remainder = n % 2;
        let quotient = n / 2;
        lemma_Str2Int_to_bit_seq(quotient);
        assert(to_bit_seq(n) == to_bit_seq(quotient).snoc(if remainder == 1 { '1' } else { '0' }));
        assert(Str2Int(to_bit_seq(n)) == 2 * Str2Int(to_bit_seq(quotient)) + (if remainder == 1 { 1nat } else { 0nat }));
        assert(Str2Int(to_bit_seq(n)) == 2 * quotient + remainder.spec_to_int().to_nat());
        assert(n == 2 * quotient + remainder.spec_to_int().to_nat());
    } else if n == 1 {
        assert(to_bit_seq(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else { // n == 0
        assert(to_bit_seq(0) == seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): uses to_bit_seq for calculation */
{
  let n_int_1 = Str2Int(s1@);
  let n_int_2 = Str2Int(s2@);
  let diff = n_int_1 - n_int_2;
  let bit_seq_diff = to_bit_seq(diff);

  proof {
    lemma_Str2Int_to_bit_seq(diff);
  }
  return Vec::from_seq(bit_seq_diff);
}
// </vc-code>

fn main() {}
}


