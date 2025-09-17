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
exec fn str_to_int(s: &[char]) -> (res: nat)
  requires ValidBitString(s@)
  ensures res == Str2Int(s@)
{
  let mut result: nat = 0nat;
  let mut i = 0;
  while i < s.len()
    invariant 
      0 <= i <= s.len(),
      ValidBitString(s@),
      result == Str2Int(s@.subrange(0, i as int))
  {
    result = result * 2nat + (if s[i] == '1' { 1nat } else { 0nat });
    i += 1;
  }
  result
}

exec fn int_to_str(n: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == n
{
  if n == 0nat {
    let mut v = Vec::new();
    v.push('0');
    return v;
  }
  
  let mut result = Vec::new();
  let mut temp = n;
  
  while temp > 0nat
    invariant ValidBitString(result@)
  {
    if temp % 2nat == 0nat {
      result.push('0');
    } else {
      result.push('1');
    }
    temp = temp / 2nat;
  }
  
  // Reverse to get most significant bit first
  let mut final_result = Vec::new();
  let mut i = result.len();
  while i > 0
    invariant ValidBitString(final_result@)
  {
    i -= 1;
    final_result.push(result[i]);
  }
  
  final_result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  let x = str_to_int(sx);
  let y = str_to_int(sy);
  let z = str_to_int(sz);
  
  if y == 0nat {
    return int_to_str(1nat % z);
  }
  
  let mut result: nat = 1nat;
  let mut base = x % z;
  let mut exp = y;
  
  while exp > 0nat
    invariant 
      result < z,
      base < z,
      (result * Exp_int(base, exp)) % z == Exp_int(x, y) % z
  {
    if exp % 2nat == 1nat {
      result = (result * base) % z;
    }
    base = (base * base) % z;
    exp = exp / 2nat;
  }
  
  int_to_str(result)
}
// </vc-code>

fn main() {}
}