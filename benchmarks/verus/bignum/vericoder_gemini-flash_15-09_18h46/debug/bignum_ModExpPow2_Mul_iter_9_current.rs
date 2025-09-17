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
/* code modified by LLM (iteration 9): Fixed type mismatch in `(temp as nat) % 2` by making `temp` a `ghost` variable instead of `u128`. */
{
  let n1 = Str2Int(s1@);
  let n2 = Str2Int(s2@);
  let product = n1 * n2;

  let mut result: Vec<char> = Vec::new();
  let ghost mut temp: nat;

  if product == 0 {
    temp = 0;
  } else {
    temp = product;
  }

  if temp == 0 {
    result.push('0');
    return result;
  }

  while temp > 0
    invariant
      temp >= 0,
      Str2Int(result@) * Exp_int(2, result@.len() as nat) + temp == product
    decreases temp
  {
    if temp % 2 == 1 {
      result.insert(0, '1');
    } else {
      result.insert(0, '0');
    }
    temp = (temp / 2) as nat;
  }

  result
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Fixed type mismatch in `(temp as nat) % 2` by making `temp` a `ghost` variable instead of `u128`. Also made `k` a ghost variable instead of `u128`. */
{
  let x_int = Str2Int(sx@);
  let y_int = Str2Int(sy@);
  let z_int = Str2Int(sz@);

  if n == 0 {
    let mut res = Vec::new();
    res.push('1'); // x^0 = 1
    return res;
  }

  if y_int == 0 {
    let mut res = Vec::new();
    res.push('1');
    return res;
  }

  let mut current_exp_val: nat = x_int;
  let ghost mut k: nat = 0;
  let ghost n_nat: nat = n as nat;

  while k < n_nat
    invariant
      current_exp_val == Exp_int(x_int, Exp_int(2, k)) % z_int,
      k >= 0,
      k <= n_nat
    decreases (n_nat - k)
  {
    current_exp_val = (current_exp_val * current_exp_val) % z_int;
    k = k + 1;
  }

  let final_val = current_exp_val;

  let mut result_vec = Vec::new();
  let ghost mut temp: nat;

  if final_val == 0 {
    temp = 0;
  } else {
    temp = final_val;
  }

  if temp == 0 {
    result_vec.push('0');
    return result_vec;
  }

  while temp > 0
    invariant
      temp >= 0,
      Str2Int(result_vec@) * Exp_int(2, result_vec@.len() as nat) + temp == final_val
    decreases temp
  {
    if temp % 2 == 1 {
      result_vec.insert(0, '1');
    } else {
      result_vec.insert(0, '0');
    }
    temp = (temp / 2) as nat;
  }
  result_vec
}
// </vc-code>

fn main() {}
}


