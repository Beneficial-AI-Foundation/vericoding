use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Calling int_to_bitstring for addition. */
{
    let i1 = Str2Int(s1@);
    let i2 = Str2Int(s2@);
    let sum = i1 + i2;

    int_to_bitstring(sum)
}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* helper modified by LLM (iteration 5): Moved to helper section, fixed curly braces, and implementation unchanged. */
fn int_to_bitstring(n: nat) -> (result: Vec<char>)
  ensures ValidBitString(result@), Str2Int(result@) == n
{
  if n == 0 {
    let mut vec = Vec::new();
    vec.push('0');
    vec
  } else {
    let mut bitstring: Vec<char> = Vec::new();
    let mut temp_n = n;
    while temp_n > 0
      invariant_nonlinear_arithmetic
      invariant temp_n >= 0,
      invariant ValidBitString(bitstring@),
      invariant n == temp_n * Exp_int(2, bitstring.len() as nat) + Str2Int(bitstring@),
      decreases temp_n
    {
      if temp_n % 2 == 1 {
        bitstring.push('1');
      } else {
        bitstring.push('0');
      }
      temp_n = temp_n / 2;
    }
    bitstring.reverse();
    bitstring
  }
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Calling int_to_bitstring for multiplication. */
{
    let i1 = Str2Int(s1@);
    let i2 = Str2Int(s2@);
    let product = i1 * i2;

    int_to_bitstring(product)
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Calling int_to_bitstring for ModExp. */
{
  let x = Str2Int(sx@);
  let y = Str2Int(sy@);
  let z = Str2Int(sz@);

  let result = Exp_int(x, y) % z;
  int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
