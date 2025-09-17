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
/* code modified by LLM (iteration 2): Fixed indexing and type conversions for `Add` function. */
{
  let mut s1_vec = s1.to_vec();
  let mut s2_vec = s2.to_vec();
  let mut result = Vec::new();
  let mut carry: nat = 0;
  let mut i: int = 0;
  let mut j: int = 0;

  while i < s1_vec.len() as int || j < s2_vec.len() as int || carry > 0
    invariant
      i <= s1_vec.len() as int,
      j <= s2_vec.len() as int,
      carry == 0 || carry == 1,
      ValidBitString(result@),
      forall |k: int| 0 <= k && k < result.len() ==> (
        result@[k] == '0' || result@[k] == '1'
      )
    decreases (s1_vec.len() as int - i) + (s2_vec.len() as int - j) + (if carry == 0 { 0 } else { 1 })
  {

    let digit1 = if i < s1_vec.len() as int { 
        (s1_vec@[i]).to_digit(10).unwrap() as nat
        
    } else { 0 };
    let digit2 = if j < s2_vec.len() as int { 
        (s2_vec@[j]).to_digit(10).unwrap() as nat
         } else { 0 };

    let sum = digit1 + digit2 + carry;
    carry = sum / 2;
    result.push(if sum % 2 == 1 { '1' } else { '0' });

    i = i + 1;
    j = j + 1;
  }

  while result.len() > 1 && result.last().unwrap() == &'0' 
    invariant
      result.len() >= 0,
      ValidBitString(result@)
  {
    result.pop();
  }

  result.reverse();
  result
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
/* helper modified by LLM (iteration 2): Added helper function to convert nat to bit string. */
fn int_to_bit_string(n: nat) -> Vec<char>
  ensures ValidBitString(result@), Str2Int(result@) == n
{
  if n == 0 {
    return vec!['0'];
  }
  let mut res_vec: Vec<char> = Vec::new();
  let mut temp_n = n;
  while temp_n > 0
    invariant
      temp_n >= 0,
      ValidBitString(res_vec@)
    decreases temp_n
  {
    if temp_n % 2 == 1 {
      res_vec.push('1');
    } else {
      res_vec.push('0');
    }
    temp_n = temp_n / 2;
  }
  res_vec.reverse();
  res_vec
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Used helper `int_to_bit_string` for multiplication. */
{
  let n1 = Str2Int(s1@);
  let n2 = Str2Int(s2@);

  let product = n1 * n2;

  int_to_bit_string(product)
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
/* code modified by LLM (iteration 2): Casted `nat` to `int` within the while loop of ModExp. */
{
  let x = Str2Int(sx@);
  let y = Str2Int(sy@);
  let z = Str2Int(sz@);

  let mut res = 1 nat;
  let mut base = x % z;
  let mut exp = y;
  
  while exp > 0
    invariant
      exp >= 0,
      res >= 0,
      base >= 0,
      z > 1,
      (res * Exp_int(base, exp)) % z == Exp_int(x,y) % z
    decreases exp
  {
    if (exp as int) % 2 == 1 {
      res = (res * base) % z;
    }
    base = (base * base) % z;
    exp = exp / 2;
  }
  
  int_to_bit_string(res)
}
// </vc-code>

fn main() {}
}
