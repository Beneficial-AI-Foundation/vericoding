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
/* code modified by LLM (iteration 4): Fixed type mismatches by casting to `nat` where necessary. */
{
  let mut result = Vec::new();
  let mut carry: nat = 0; // Changed to nat
  let mut i: int = 0;
  let mut j: int = 0;

  while i < s1.len() as int || j < s2.len() as int || carry > 0
    invariant (
      carry >= 0 && carry <= 2,
      ValidBitString(result@),
      true
    )
    decreases (s1.len() as int - i) + (s2.len() as int - j) + carry as int
  {
    let mut bit1: nat = 0;
    if i < s1.len() as int {
      if s1[s1.len() as int - 1 - i] == '1' { bit1 = 1nat; }
      i += 1;
    }

    let mut bit2: nat = 0;
    if j < s2.len() as int {
      if s2[s2.len() as int - 1 - j] == '1' { bit2 = 1nat; }
      j += 1;
    }

    let sum: nat = bit1 + bit2 + carry;
    result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
    carry = (sum / 2) as nat; // Cast result to nat
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
/* code modified by LLM (iteration 4): Fixed type mismatches. */
{
  let s1_int = Str2Int(s1@);
  let s2_int = Str2Int(s2@);
  let mut product: nat = s1_int * s2_int;
  
  if product == 0nat {
      return vec!['0'];
  }

  let mut res_vec = Vec::new();
  while product > 0nat
    invariant (product >= 0)
    decreases product
  {
    if product % 2 == 1nat {
      res_vec.insert(0, '1');
    } else {
      res_vec.insert(0, '0');
    }
    product = (product / 2) as nat;
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
/* code modified by LLM (iteration 4): Fixed type mismatches for `n` and comparison with `int`. */
{
  if n == 0 {
    let final_x_val = Str2Int(sx@);
    let final_z_val = Str2Int(sz@);
    let result_val = final_x_val % final_z_val;
    
    if result_val == 0nat {
        return vec!['0'];
    }

    let mut res_vec = Vec::new();
    let mut temp_result = result_val;
    while temp_result > 0nat
        invariant (temp_result >= 0)
        decreases temp_result
    {
        if temp_result % 2 == 1nat {
            res_vec.insert(0, '1');
        } else {
            res_vec.insert(0, '0');
        }
        temp_result = (temp_result / 2) as nat;
    }
    return res_vec;
  }

  let sy_val = Str2Int(sy@);

  if sy_val == 0nat {
    let one_vec = vec!['1'];
    return one_vec;
  }

  let mut current_x_val = Str2Int(sx@);
  let z_val = Str2Int(sz@);
  let mut result_val: nat = current_x_val % z_val;
  
  let mut k: int = 0;
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
  
  if result_val == 0nat {
    return vec!['0'];
  }

  let mut res_vec = Vec::new();
  let mut temp_result = result_val;
  while temp_result > 0nat
    invariant (temp_result >= 0)
    decreases temp_result
  {
    if temp_result % 2 == 1nat {
      res_vec.insert(0, '1');
    } else {
      res_vec.insert(0, '0');
    }
    temp_result = (temp_result / 2) as nat;
  }
  res_vec
}
// </vc-code>

fn main() {}
}
