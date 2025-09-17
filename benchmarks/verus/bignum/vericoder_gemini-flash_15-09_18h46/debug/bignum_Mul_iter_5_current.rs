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
/* helper modified by LLM (iteration 5): Fixed typo in proof fn name. */
proof fn proof_Str2Int_double_seq(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + seq!['0']) == 2 * Str2Int(s)
{
    if s.len() == 0 {
        assert(s + seq!['0'] =~= seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
        assert(Str2Int(s) == 0);
    } else {
        assert(Str2Int(s + seq!['0']) == 2 * Str2Int(s));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type inconsistencies and cast errors by ensuring all loop conditions and indexing operations use `usize` for lengths and `int` for sequence indexing where appropriate. */
{
  proof_multiply_bit_strings(s1@, s2@);
  let res_seq = multiply_bit_strings_spec(s1@, s2@);
  let mut res_vec = Vec::<char>::new();
  let mut i: usize = 0;
  while i < res_seq.len()
    invariant
      0 <= i,
      i <= res_seq.len(),
      res_vec.len() == i,
      forall |j: int| 0 <= j && j < i as int ==> #[trigger] res_vec.index(j) == res_seq.index(j),
      ValidBitString(res_vec@)
  {
    res_vec.push(res_seq.index(i as int));
    i = i + 1;
  }
  res_vec
}
// </vc-code>

fn main() {}
}


