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
/* code modified by LLM (iteration 3): Fixed compilation errors by ensuring all integer literals are correctly typed as `nat` or `int` and converted `usize` to `int` for comparisons. Also fixed indexing `s1_vec@[i]` for Seq<char>. */
{
  let mut result: Vec<char> = Vec::new();
  let mut carry: nat = 0; // Fixed: type `nat`
  let mut i: int = 0;     // Fixed: type `int`

  let mut s1_vec = s1.to_vec();
  let mut s2_vec = s2.to_vec();

  s1_vec.reverse();
  s2_vec.reverse();

  let max_len_int = if (s1_vec.len() as int) > (s2_vec.len() as int) { s1_vec.len() as int } else { s2_vec.len() as int }; // Fixed: Use int for max_len

  while i < max_len_int || carry == 1nat // Fixed: type `nat`, compare with `nat`
    invariant
      result.len() as int == i,
      carry == 0nat || carry == 1nat,
      ValidBitString(result@),
      i <= max_len_int + 1
    decreases max_len_int - i + carry as int
  {
    proof {
      if (0 <= i && i < result.len() as int) { // Fixed: cast to int
        let b1 = if i < s1_vec.len() as int { if s1_vec@[i] == '1' { 1nat } else { 0nat } } else { 0nat }; // Fixed: cast to int, use nat
        let b2 = if i < s2_vec.len() as int { if s2_vec@[i] == '1' { 1nat } else { 0nat } } else { 0nat }; // Fixed: cast to int, use nat
        let _ = (b1 + b2 + (if i == 0 { 0nat } else { (if result@[i-1] == '1' { 1nat } else { 0nat })})) % 2 nat;
      }
    }

    let mut digit1: nat = 0; // Fixed: type `nat`
    if i < s1_vec.len() as int { // Fixed: Compare with int
      digit1 = if s1_vec@[i] == '1' { 1nat } else { 0nat }; // Fixed: use nat and cast to int for index
    }

    let mut digit2: nat = 0; // Fixed: type `nat`
    if i < s2_vec.len() as int { // Fixed: Compare with int
      digit2 = if s2_vec@[i] == '1' { 1nat } else { 0nat }; // Fixed: use nat and cast to int for index
    }

    let sum:nat = digit1 + digit2 + carry;
    let current_digit: nat = sum % 2nat; // Fixed: type `nat` and use nat literal
    carry = sum / 2nat; // Fixed: type `nat` and use nat literal

    result.push(if current_digit == 1nat { '1' } else { '0' }); // Fixed: compare with `nat`
    i = i + 1; // Fixed: `i` is `int`
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
/* code modified by LLM (iteration 3): Fixed compilation errors by ensuring all integer literals are correctly typed as `nat` or `int` and converted `usize` to `int` for comparisons. */
{
  let mut res_vec: Vec<char> = Vec::new();

  if s1.len() == 0 || s2.len() == 0 {
    res_vec.push('0');
    return res_vec;
  }

  let s1_nat = Str2Int(s1@);
  let s2_nat = Str2Int(s2@);
  let product_nat = s1_nat * s2_nat;

  if product_nat == 0nat { // Fixed: type `nat`
    res_vec.push('0');
    return res_vec;
  }

  let mut temp_product = product_nat;
  while temp_product > 0nat // Fixed: type `nat`
    invariant
      ValidBitString(res_vec@),
      temp_product * Exp_int(2nat, res_vec.len() as nat) + Str2Int(res_vec@) == product_nat
    decreases temp_product
  {
    let digit: nat = temp_product % 2nat; // Fixed: type `nat`
    if digit == 1nat { // Fixed: type `nat`
      res_vec.push('1');
    } else {
      res_vec.push('0');
    }
    temp_product = temp_product / 2nat; // Fixed: type `nat`
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
/* code modified by LLM (iteration 3): Fixed compilation errors by ensuring all integer literals are correctly typed as `nat` or `int` and converted `usize` to `int` for comparisons. Addressed the modulo operator error by ensuring both operands are of type `nat` or consistent integer types. */
{
  let x_nat = Str2Int(sx@);
  let y_nat = Str2Int(sy@);
  let z_nat = Str2Int(sz@);

  let mut result_nat: nat;

  if y_nat == 0nat { // Fixed: type `nat`
    result_nat = 1nat % z_nat; // Fixed: use `1nat`
  } else {
    let mut base: nat = x_nat % z_nat;
    let mut exp: nat = y_nat;
    let mut res_acc: nat = 1; // Fixed: type `nat`

    while exp > 0nat // Fixed: type `nat`
      invariant
        exp >= 0nat,
        res_acc > 0nat,
        base >= 0nat,
        z_nat > 1nat
      decreases exp
    {
      if exp % 2nat == 1nat { // Fixed: type `nat`
        res_acc = (res_acc * base) % z_nat;
      }
      base = (base * base) % z_nat;
      exp = exp / 2nat; // Fixed: type `nat`
    }
    result_nat = res_acc;
  }

  let mut res_vec: Vec<char> = Vec::new();
  if result_nat == 0nat { // Fixed: type `nat`
    res_vec.push('0');
  } else {
    let mut temp = result_nat;
    while temp > 0nat // Fixed: type `nat`
      invariant
        ValidBitString(res_vec@),
        temp * Exp_int(2nat, res_vec.len() as nat) + Str2Int(res_vec@) == result_nat
      decreases temp
    {
      let digit: nat = temp % 2nat; // Fixed: type `nat`
      if digit == 1nat { // Fixed: type `nat`
        res_vec.push('1');
      } else {
        res_vec.push('0');
      }
      temp = temp / 2nat; // Fixed: type `nat`
    }
    res_vec.reverse();
  }

  return res_vec;
}
// </vc-code>

fn main() {}
}


