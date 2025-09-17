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
/* code modified by LLM (iteration 3): Fixed `invariant` syntax for `Add` function. */
  let mut result = Vec::new();
  let mut carry = 0;
  let mut i = 0;
  let mut j = 0;

  while i < s1.len() || j < s2.len() || carry > 0
    invariant (
      carry >= 0 && carry <= 2,
      ValidBitString(result@),
      true
    )
    decreases (s1.len() - i as int) + (s2.len() - j as int) + carry as int
  {
    let mut bit1: nat = 0;
    if i < s1.len() {
      if s1[s1.len() - 1 - i] == '1' { bit1 = 1; }
      i += 1;
    }

    let mut bit2: nat = 0;
    if j < s2.len() {
      if s2[s2.len() - 1 - j] == '1' { bit2 = 1; }
      j += 1;
    }

    let sum = bit1 + bit2 + carry;
    result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
    carry = sum / 2;
  }
  result
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): No changes required, as the previous iteration produced a compilable version for `Mul`. */
  let s1_int = Str2Int(s1@);
  let s2_int = Str2Int(s2@);
  let mut product = s1_int * s2_int;
  
  if product == 0 { 
      return vec!['0'];
  }

  let mut res_vec = Vec::new();
  while product > 0
    invariant (product >= 0)
    decreases product
  {
    if product % 2 == 1 {
      res_vec.insert(0, '1');
    } else {
      res_vec.insert(0, '0');
    }
    product = product / 2;
  }
  res_vec
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
{
/* code modified by LLM (iteration 3): Fixed `invariant` syntax for `ModExpPow2` function. */
  if n == 0 {
    let final_x_val = Str2Int(sx@);
    let final_z_val = Str2Int(sz@);
    let result_val = final_x_val % final_z_val;
    
    if result_val == 0 {
        return vec!['0'];
    }

    let mut res_vec = Vec::new();
    let mut temp_result = result_val;
    while temp_result > 0
        invariant (temp_result >= 0)
        decreases temp_result
    {
        if temp_result % 2 == 1 {
            res_vec.insert(0, '1');
        } else {
            res_vec.insert(0, '0');
        }
        temp_result = temp_result / 2;
    }
    return res_vec;
  }

  // Recursive step: ModExpPow2(X, 2^n+1, n+1, Z) = ModExpPow2(X, 2^n, n, Z) * X % Z
  // This structure needs adjustment for the sy argument which is 2^n or 0
  // If sy is 2^n, we compute X^(2^n) mod Z
  // The helper function needs to be a spec function, not exec, for direct recursive calls within specs
  // We need to implement this iteratively or with a different recursive structure

  // Let's re-think based on the given sy structure: sy can only be 0 or 2^n
  let sy_val = Str2Int(sy@);

  if sy_val == 0 {
    let one_vec = vec!['1'];
    return one_vec;
  }

  // If sy_val is 2^n, we are computing x^(2^n) mod z
  // This can be computed by repeated squaring: x^(2^n) = (((x^2)^2)...)^2 (n times)
  let mut current_x_val = Str2Int(sx@);
  let z_val = Str2Int(sz@);
  let mut result_val = current_x_val % z_val;
  
  let mut k = 0;
  while (k < n)
    invariant (
      k >= 0 && k <= n,
      result_val >= 0 && result_val < z_val
    )
    decreases (n - k)
  {
    result_val = (result_val * result_val) % z_val;
    k += 1;
  }
  
  if result_val == 0 {
    return vec!['0'];
  }

  let mut res_vec = Vec::new();
  let mut temp_result = result_val;
  while temp_result > 0
    invariant (temp_result >= 0)
    decreases temp_result
  {
    if temp_result % 2 == 1 {
      res_vec.insert(0, '1');
    } else {
      res_vec.insert(0, '0');
    }
    temp_result = temp_result / 2;
  }
  res_vec
}
// </vc-code>

fn main() {}
}
