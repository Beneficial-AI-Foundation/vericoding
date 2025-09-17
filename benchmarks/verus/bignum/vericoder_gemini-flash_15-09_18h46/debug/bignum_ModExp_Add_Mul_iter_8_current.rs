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
/* code modified by LLM (iteration 8): Fixed nat literal syntax in let statement. */
{
  let mut result: Vec<char> = Vec::new();
  let mut carry: nat = 0; // Fix: Removed 'nat' suffix
  let mut i: usize = 0;

  let s1_vec = s1.to_vec();
  let s2_vec = s2.to_vec();

  let max_len = if s1_vec.len() > s2_vec.len() { s1_vec.len() } else { s2_vec.len() };

  while i < max_len || carry == (1 as nat)
    invariant
      result.len() == i,
      carry == (0 as nat) || carry == (1 as nat),
      i <= max_len + 1
    decreases max_len + 1 - i
  {
    let mut digit1: nat = 0;
    if i < s1_vec.len() {
      digit1 = if s1_vec[s1_vec.len() - 1 - i] == '1' { 1 } else { 0 };
    }

    let mut digit2: nat = 0;
    if i < s2_vec.len() {
      digit2 = if s2_vec[s2_vec.len() - 1 - i] == '1' { 1 } else { 0 };
    }

    let sum: nat = digit1 + digit2 + carry;
    let current_digit: nat = sum % (2 as nat);
    carry = sum / (2 as nat);

    result.push(if current_digit == (1 as nat) { '1' } else { '0' });
    i = i + 1;
  }

  result.reverse();
  return result;
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): Fixed nat literal syntax in let statement. */
{
  let mut res_vec: Vec<char> = Vec::new();

  if s1.len() == 0 || s2.len() == 0 {
    res_vec.push('0');
    return res_vec;
  }

  let s1_nat = Str2Int(s1@);
  let s2_nat = Str2Int(s2@);
  let product_nat = s1_nat * s2_nat;

  if product_nat == (0 as nat) {
    res_vec.push('0');
    return res_vec;
  }

  let mut temp_product: nat = product_nat;
  while temp_product > (0 as nat)
    invariant
      ValidBitString(res_vec@),
      temp_product * Exp_int(2 as nat, res_vec.len() as nat) + Str2Int(res_vec@) == product_nat
    decreases temp_product
  {
    let digit: nat = temp_product % (2 as nat);
    if digit == (1 as nat) {
      res_vec.push('1');
    } else {
      res_vec.push('0');
    }
    temp_product = temp_product / (2 as nat);
  }

  res_vec.reverse();
  return res_vec;
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
/* code modified by LLM (iteration 8): Fixed nat literal syntax in let statement. */
{
  let x_nat = Str2Int(sx@);
  let y_nat = Str2Int(sy@);
  let z_nat = Str2Int(sz@);

  let mut result_nat: nat;

  if y_nat == (0 as nat) {
    result_nat = (1 as nat) % z_nat;
  } else {
    let mut base: nat = x_nat % z_nat;
    let mut exp: nat = y_nat;
    let mut res_acc: nat = 1; // Fix: Removed 'nat' suffix

    while exp > (0 as nat)
      invariant
        exp >= (0 as nat),
        res_acc >= (0 as nat),
        base >= (0 as nat),
        z_nat > (1 as nat),
        true
      decreases exp
    {
      if exp % (2 as nat) == (1 as nat) {
        res_acc = (res_acc * base) % z_nat;
      }
      base = (base * base) % z_nat;
      exp = exp / (2 as nat);
    }
    result_nat = res_acc;
  }

  let mut res_vec: Vec<char> = Vec::new();
  if result_nat == (0 as nat) {
    res_vec.push('0');
  } else {
    let mut temp: nat = result_nat;
    while temp > (0 as nat)
      invariant
        ValidBitString(res_vec@),
        temp * Exp_int(2 as nat, res_vec.len() as nat) + Str2Int(res_vec@) == result_nat
      decreases temp
    {
      let digit: nat = temp % (2 as nat);
      if digit == (1 as nat) {
        res_vec.push('1');
      } else {
        res_vec.push('0');
      }
      temp = temp / (2 as nat);
    }
    res_vec.reverse();
  }

  return res_vec;
}
// </vc-code>

fn main() {}
}


