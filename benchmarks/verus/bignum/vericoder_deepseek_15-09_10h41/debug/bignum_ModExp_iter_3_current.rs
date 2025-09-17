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
/* helper modified by LLM (iteration 3): fix nat literal syntax and add proper type conversions */
proof fn lemma_mod_exp_property(x: nat, y: nat, z: nat)
  requires z > 0
  ensures y > 0 ==> Exp_int(x, y) % z == ((x % z) * Exp_int(x % z, (y - 1) as nat)) % z
  decreases y
{
  if y > 0 {
    let exp_minus_one = Exp_int(x, (y - 1) as nat);
    let x_mod_z = x % z;
    assert(Exp_int(x, y) == x * exp_minus_one);
    assert((x * exp_minus_one) % z == ((x % z) * (exp_minus_one % z)) % z);
    lemma_mod_exp_property(x, (y - 1) as nat, z);
  }
}

proof fn lemma_exp_mod_base(x: nat, z: nat)
  requires z > 0
  ensures Exp_int(x % z, 0) == 1
{
}

proof fn lemma_mod_mul_property(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a % z) * (b % z) % z == (a * b) % z
{
}

spec fn nat_to_int(n: nat) -> int {
  n as int
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
/* code modified by LLM (iteration 3): fix nat literal syntax and type conversion issues */
{
  let mut base = Str2Int(sx@) % Str2Int(sz@);
  let mut exponent = Str2Int(sy@);
  let modulus = Str2Int(sz@);
  let mut result: nat = 1;
  
  while exponent > 0
    invariant
      result * Exp_int(base, exponent) % modulus == Exp_int(Str2Int(sx@), Str2Int(sy@)) % modulus,
      base < modulus,
      0 < modulus
    decreases exponent
  {
    if exponent % 2 == 1 {
      result = (result * base) % modulus;
    }
    base = (base * base) % modulus;
    exponent = exponent / 2;
  }
  
  // Convert result to binary representation
  let mut temp = result;
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


