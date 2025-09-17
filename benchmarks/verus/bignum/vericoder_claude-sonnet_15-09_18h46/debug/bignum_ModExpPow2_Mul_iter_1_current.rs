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
{
    if s1.len() == 0 || s2.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    let mut i = 0;
    
    while i < s1.len()
        invariant
            i <= s1.len(),
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@.subrange(0, i as int)) * Str2Int(s2@)
    {
        if s1[i] == '1' {
            let temp = Mul(&result, s2);
            result = temp;
        }
        i += 1;
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
{
    if Str2Int(sy@) == 0 {
        return vec!['1'];
    }
    
    if n == 0 {
        if sy[0] == '1' {
            let x_mod_z = ModExp(sx, &vec!['1'], sz);
            return x_mod_z;
        } else {
            return vec!['1'];
        }
    }
    
    let sy_half = &sy@.subrange(1, sy@.len() as int);
    let sy_half_vec: Vec<char> = sy_half.into_iter().collect();
    
    let temp = ModExpPow2(sx, &sy_half_vec, n - 1, sz);
    let squared = Mul(&temp, &temp);
    let squared_mod = ModExp(&squared, &vec!['1'], sz);
    
    if sy[0] == '1' {
        let x_mod = ModExp(sx, &vec!['1'], sz);
        let final_result = Mul(&squared_mod, &x_mod);
        ModExp(&final_result, &vec!['1'], sz)
    } else {
        squared_mod
    }
}
// </vc-code>

fn main() {}
}


