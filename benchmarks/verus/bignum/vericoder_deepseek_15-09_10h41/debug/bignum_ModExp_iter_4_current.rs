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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
/* helper modified by LLM (iteration 4): fix nat type conversions and add proper nat operations */
proof fn lemma_nat_div_floor(a: nat, b: nat) -> (q: nat)
  requires b > 0
  ensures q * b <= a < (q + 1) * b
{
  if a < b {
    0
  } else {
    let q_prime = lemma_nat_div_floor(a - b, b);
    q_prime + 1
  }
}

proof fn lemma_nat_mod_property(a: nat, b: nat) -> (r: nat)
  requires b > 0
  ensures r == a % b, r < b
{
  if a < b {
    a
  } else {
    lemma_nat_mod_property(a - b, b)
  }
}

spec fn nat_gt_zero(n: nat) -> bool {
  n > 0
}

proof fn lemma_nat_arithmetic(a: nat, b: nat)
  requires b > 0
  ensures a % b < b, a / b * b <= a
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fix nat type conversion issues and use proper nat operations */
{
  let base_int = Str2Int(sx@) % Str2Int(sz@);
  let exponent_int = Str2Int(sy@);
  let modulus_int = Str2Int(sz@);
  
  let mut base: nat = base_int;
  let mut exponent: nat = exponent_int;
  let modulus: nat = modulus_int;
  let mut result: nat = 1;
  
  while exponent > 0
    invariant
      result * Exp_int(base, exponent) % modulus == Exp_int(Str2Int(sx@), Str2Int(sy@)) % modulus,
      base < modulus,
      modulus > 1
    decreases exponent
  {
    if exponent % 2 == 1 {
      result = (result * base) % modulus;
    }
    base = (base * base) % modulus;
    exponent = exponent / 2;
  }
  
  // Convert result to binary representation
  let mut temp: nat = result;
  let mut binary_digits = Vec::new();
  
  if temp == 0 {
    binary_digits.push('0');
  } else {
    while temp > 0
      invariant
        temp >= 0,
        ValidBitString(binary_digits@)
      decreases temp
    {
      if temp % 2 == 1 {
        binary_digits.push('1');
      } else {
        binary_digits.push('0');
      }
      temp = temp / 2;
    }
    binary_digits.reverse();
  }
  
  binary_digits
}
// </vc-code>

fn main() {}
}


