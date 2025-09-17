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
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    if sy@.len() == 0 || Str2Int(sy@) == 0 {
        return vec!['1'];
    }
    
    let mut result = vec!['1'];
    let mut base = sx.to_vec();
    let mut exp = sy.to_vec();
    
    while Str2Int(exp@) > 0
        invariant
            ValidBitString(result@),
            ValidBitString(base@),
            ValidBitString(exp@),
            Str2Int(result@) * Exp_int(Str2Int(base@), Str2Int(exp@)) % Str2Int(sz@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
    {
        if exp[exp.len() - 1] == '1' {
            let temp = multiply_mod(&result, &base, sz);
            result = temp;
        }
        
        let temp_base = multiply_mod(&base, &base, sz);
        base = temp_base;
        
        exp = divide_by_two(&exp);
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
    if n == 0 {
        if sy@.len() == 1 && sy@[0] == '1' {
            let (_, remainder) = DivMod(sx, sz);
            return remainder;
        } else {
            return vec!['1'];
        }
    }
    
    let half_n = n / 2;
    let mut half_exp = vec!['0'; half_n as usize + 1];
    half_exp[half_n as usize] = '1';
    
    let half_result = ModExpPow2(sx, &half_exp, half_n, sz);
    let squared = multiply_mod(&half_result, &half_result, sz);
    
    if n % 2 == 0 {
        squared
    } else {
        let extra_result = ModExpPow2(sx, &vec!['1'], 0, sz);
        multiply_mod(&squared, &extra_result, sz)
    }
}
// </vc-code>

fn main() {}
}


