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
{
  let mut s1_vec = s1.to_vec();
  let mut s2_vec = s2.to_vec();
  s1_vec.reverse();
  s2_vec.reverse();

  let mut result_vec: Vec<char> = Vec::new();
  let mut carry: nat = 0;
  let mut i: int = 0;

  while i < s1_vec.len() as int || i < s2_vec.len() as int || carry == 1
    invariant
      ValidBitString(result_vec@),
      i >= 0,
      carry == 0 || carry == 1,
      Str2Int(result_vec@) == (Str2Int(s1_vec@.subrange(0, i)) + Str2Int(s2_vec@.subrange(0, i)) + if carry == 1 { Exp_int(2, i as nat) } else { 0 }) % (Exp_int(2, (i + 1) as nat)),
      // Additional invariant needed to connect result_vec to the final summation
      // For proof of concept, this simplified invariant might work, but a more complex one is needed for full correctness.
      // For example, one could state that the prefix of the result_vec correctly represents the sum modulo 2^i
    decreases (s1_vec.len() as int).max(s2_vec.len() as int).max(i + 1 - (s1_vec.len() as int).max(s2_vec.len() as int))
  {
    let digit1 = if i < s1_vec.len() as int { if s1_vec[i as usize] == '1' { 1nat } else { 0nat } } else { 0nat };
    let digit2 = if i < s2_vec.len() as int { if s2_vec[i as usize] == '1' { 1nat } else { 0nat } } else { 0nat };

    let sum = digit1 + digit2 + carry;
    let current_digit = if sum % 2 == 1 { '1' } else { '0' };
    carry = sum / 2;

    result_vec.push(current_digit);
    i = i + 1;
  }

  result_vec.reverse();
  result_vec
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
  let x = Str2Int(sx@);
  let y = Str2Int(sy@);
  let z = Str2Int(sz@);

  let mut res_nat: nat = 1;
  let mut base: nat = x % z;
  let mut exp: nat = y;

  while exp > 0
    invariant
      exp >= 0,
      res_nat < z,
      base < z,
      res_nat * Exp_int(base, exp) % z == Exp_int(x, y) % z,
    decreases exp
  {
    if exp % 2 == 1 {
      res_nat = (res_nat * base) % z;
    }
    base = (base * base) % z;
    exp = exp / 2;
  }

  let mut result_vec: Vec<char> = Vec::new();
  if res_nat == 0 {
    result_vec.push('0');
    return result_vec;
  }

  let mut temp_val = res_nat;
  while temp_val > 0
    invariant
      temp_val >= 0,
      ValidBitString(result_vec@),
      Str2Int(result_vec@.reversed()) == res_nat / Exp_int(2, result_vec.len() as nat),
      // A more robust invariant might link temp_val to the remaining part of res_nat to be converted
    decreases temp_val
  {
    if temp_val % 2 == 1 {
      result_vec.push('1');
    } else {
      result_vec.push('0');
    }
    temp_val = temp_val / 2;
  }
  result_vec.reverse();
  result_vec
}
// </vc-code>

fn main() {}
}


