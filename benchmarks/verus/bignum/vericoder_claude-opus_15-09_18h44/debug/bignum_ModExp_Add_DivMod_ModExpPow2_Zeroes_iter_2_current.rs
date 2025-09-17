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

// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type error by using usize for indexing */
{
  let ghost a_val = Str2Int(a@);
  let ghost b_val = Str2Int(b@);  
  let ghost sum = a_val + b_val;
  
  proof {
    lemma_str2int_int2str(sum);
  }
  
  let mut result = Vec::<char>::new();
  let ghost sum_str = Int2Str(sum);
  
  let mut i: usize = 0;
  while i < sum_str.len()
    invariant
      i <= sum_str.len(),
      result@.len() == i as int,
      forall |j: int| 0 <= j && j < i as int ==> result@[j] == sum_str[j],
      ValidBitString(result@)
  {
    result.push(sum_str[i as int]);
    i = i + 1;
  }
  
  result
}
// </vc-code>

fn main() {}
}

