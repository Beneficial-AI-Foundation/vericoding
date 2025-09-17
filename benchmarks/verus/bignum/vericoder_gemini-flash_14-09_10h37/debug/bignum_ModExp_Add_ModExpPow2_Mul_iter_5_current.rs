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
/* helper modified by LLM (iteration 5): removed requires/ensures from spec fn */
spec fn add_bit_strings_spec(a: Seq<char>, b: Seq<char>) -> Seq<char>
{
  let x = Str2Int(a);
  let y = Str2Int(b);
  let sum = x + y;

  int_to_bit_seq(sum)
}

spec fn int_to_bit_seq(n: nat) -> Seq<char>
{
  if n == 0 {
    Seq::empty().push('0')
  } else {
    let rem = n % 2;
    let div = n / 2;
    if div == 0 {
      if rem == 1 { Seq::empty().push('1') }
      else { Seq::empty().push('0') }
    } else {
      int_to_bit_seq(div).push(if rem == 1 { '1' } else { '0' })
    }
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): call add_bit_strings_spec and convert to Vec */
{
  let s_a = a@;
  let s_b = b@;

  let sum_seq = add_bit_strings_spec(s_a, s_b);

  let mut res_vec = Vec::<char>::new();
  let mut i = 0;
  while i < sum_seq.len()
    invariant
      0 <= i,
      i <= sum_seq.len(),
      res_vec.len() == i,
      forall |j: int| 0 <= j && j < i ==> res_vec.index(j) == sum_seq.index(j)
  {
    res_vec.push(sum_seq.index(i));
    i = i + 1;
  }
  res_vec
}
// </vc-code>

fn main() {}
}

