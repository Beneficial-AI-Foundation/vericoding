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

// <vc-helpers>
spec fn ModExpPow2_int(s_a: Seq<char>, s_b: Seq<char>, s_n: Seq<char>) -> nat
  decreases s_b.len()
{
  if s_b.len() == 0 {
    1
  } else if s_b.index(0) == '0' {
    ModExpPow2_int(s_a.subrange(1, s_b.len() as int), 2 * Str2Int(s_a) % Str2Int(s_n), s_n)
  } else {
    (Str2Int(s_a) * ModExpPow2_int(s_a.subrange(1, s_b.len() as int - 1), 2 * Str2Int(s_a) % Str2Int(s_n), s_n)) % Str2Int(s_n)
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let mut result_int: nat = 1;
    let mut base: nat = x_int % z_int;
    let mut exponent: nat = y_int;

    while exponent > 0
      invariant
        result_int * Exp_int(base, exponent) % z_int == Exp_int(x_int, y_int) % z_int,
        z_int > 1
      decreases exponent
    {
        if exponent % 2 == 1 {
            result_int = (result_int * base) % z_int;
        }
        base = (base * base) % z_int;
        exponent = exponent / 2;
    }

    // Convert the result_int (nat) back to a Vec<char> representing a bit string.
    // This part requires converting a nat to a binary string representation.

    // For simplicity, let's assume a helper `int_to_bitstring` exists or directly construct.
    // A real implementation would need to convert `result_int` to its binary string form.

    let mut char_vec: Vec<char> = Vec::new();
    let mut temp = result_int;
    if temp == 0 && z_int > 0 { // Special case for 0 (and z_int > 0 to ensure valid modulus) 
      char_vec.push('0');
    } else {
      while temp > 0
        invariant
          temp < result_int + 1,
          char_vec.len() < z_int.log_2() + 1 + 1 // Upper bound for binary rep length
        decreases temp
      {
          if temp % 2 == 1 {
              char_vec.push('1');
          } else {
              char_vec.push('0');
          }
          temp = temp / 2;
      }
    }

    char_vec.reverse();
    char_vec
}
// </vc-code>

fn main() {}
}
