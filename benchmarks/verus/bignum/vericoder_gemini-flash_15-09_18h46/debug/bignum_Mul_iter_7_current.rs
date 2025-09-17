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
/* helper modified by LLM (iteration 7): Removed the `proof fn` and corrected the `multiply_bit_strings_spec` to handle the `Str2Int` conversion and bit string generation within a `spec` context, ensuring `ValidBitString` for the result. */
spec fn multiply_bit_strings_spec(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
  requires ValidBitString(s1),
           ValidBitString(s2)
  ensures ValidBitString(result),
          Str2Int(result) == Str2Int(s1) * Str2Int(s2)
{
  let num1 = Str2Int(s1);
  let num2 = Str2Int(s2);
  let product = num1 * num2;

  if product == 0 {
    seq!['0']
  } else {
    let mut result_seq = Seq::<char>::new();
    let mut temp_product = product;
    while temp_product > 0
      invariant
        temp_product >= 0,
        ValidBitString(result_seq),
        product == Str2Int(result_seq) + temp_product * (1nat << (result_seq.len() as nat)),
    {
      if temp_product % 2 == 1 {
        result_seq = seq!['1'] + result_seq;
      } else {
        result_seq = seq!['0'] + result_seq;
      }
      temp_product = temp_product / 2;
    }
    result_seq
  }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Modified the `push` call to convert the `i` variable to `int` within a ghost context, resolving a compilation error related to using `nat` or `int` in non-ghost code. */
{
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
    // The index(i as int) correctly extracts the character as a ghost value,
    // which is then pushed into the concrete res_vec.
    res_vec.push(res_seq.index(i as int));
    i = i + 1;
  }
  res_vec
}
// </vc-code>

fn main() {}
}


