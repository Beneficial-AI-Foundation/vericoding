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
/* helper modified by LLM (iteration 3): correct lemma syntax */
lemma fn lemma_Str2Int_to_bit_seq(n: nat)
    ensures Str2Int(to_bit_seq(n)) == n
    decreases n
{
    if n > 1 {
        let remainder = n % 2;
        let quotient = n / 2;
        lemma_Str2Int_to_bit_seq(quotient);
    } else if n == 1 {
        assert(to_bit_seq(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
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
/* code modified by LLM (iteration 3): corrected to_bit_seq call */
{
  let n_int_1 = Str2Int(s1@);
  let n_int_2 = Str2Int(s2@);
  let diff = n_int_1 - n_int_2;
  lemma_Str2Int_to_bit_seq(diff);
  let res_seq = to_bit_seq(diff);
  res_seq.to_vec()
}
// </vc-code>

fn main() {}
}


