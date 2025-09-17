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
/* helper modified by LLM (iteration 3): int_to_bit_seq now handles n != 0 by recursively building the bit string */
spec fn add_bit_strings_spec(a: Seq<char>, b: Seq<char>) -> Seq<char>
  requires ValidBitString(a), ValidBitString(b)
{
  let x = Str2Int(a);
  let y = Str2Int(b);
  let sum = x + y;

  int_to_bit_seq(sum)
}

spec fn int_to_bit_seq(n: nat) -> Seq<char>
{
  if n == 0 {
    Seq::singleton('0')
  } else {
    let rem = n % 2;
    let div = n / 2;
    if div == 0 {
      if rem == 1 { Seq::singleton('1') }
      else { Seq::singleton('0') }
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
{
  /* code modified by LLM (iteration 3): replaced new_with with new and push, along with fixing the type error */
  let mut res = Vec::<char>::new();
  res.push('0'); // Mimics new_with(1, '0')
  res
}
// </vc-code>

fn main() {}
}

