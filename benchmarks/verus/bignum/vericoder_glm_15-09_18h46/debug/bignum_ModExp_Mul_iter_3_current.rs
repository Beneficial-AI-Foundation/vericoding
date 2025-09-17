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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): removed nat suffixes from number literals */
  // Convert bit strings to integers
  let x = Str2Int(s1@);
  let y = Str2Int(s2@);
  let product = x * y;
  
  // Convert product to bit string
  let mut result = Vec::<char>::new();
  let mut n = product;
  
  if n == 0 {
    result.push('0');
  } else {
    while n > 0
      invariant 0 <= n <= product
      decreases n
    {
      if n % 2 == 0 {
        result.push('0');
      } else {
        result.push('1');
      }
      n = n / 2;
    }
  }
  
  result.reverse();
  result
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
{
  /* code modified by LLM (iteration 3): removed nat suffixes from number literals */
  // Convert bit strings to integers
  let x = Str2Int(sx@);
  let y = Str2Int(sy@);
  let z = Str2Int(sz@);
  
  // Compute x^y mod z using modular exponentiation
  let mut result = 1;
  let mut base = x % z;
  let mut exp = y;
  
  while exp > 0
    invariant result >= 0, base >= 0, exp >= 0,
      result * Exp_int(base, exp) % z == Exp_int(x, y) % z
    decreases exp
  {
    if exp % 2 == 1 {
      result = (result * base) % z;
    }
    base = (base * base) % z;
    exp = exp / 2;
  }
  
  // Convert result to bit string
  let mut bit_string = Vec::<char>::new();
  let mut n = result;
  
  if n == 0 {
    bit_string.push('0');
  } else {
    while n > 0
      invariant 0 <= n <= result
      decreases n
    {
      if n % 2 == 0 {
        bit_string.push('0');
      } else {
        bit_string.push('1');
      }
      n = n / 2;
    }
  }
  
  bit_string.reverse();
  bit_string
}
// </vc-code>

fn main() {}
}
