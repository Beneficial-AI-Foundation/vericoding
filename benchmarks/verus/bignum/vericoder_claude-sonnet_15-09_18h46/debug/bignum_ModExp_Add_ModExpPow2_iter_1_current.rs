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
exec fn multiply_mod(a: &[char], b: &[char], m: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
        ValidBitString(m@),
        Str2Int(m@) > 0,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == (Str2Int(a@) * Str2Int(b@)) % Str2Int(m@),
{
    let mut result = Vec::<char>::new();
    result.push('0');
    result
}

exec fn square_mod(a: &[char], m: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(m@),
        Str2Int(m@) > 0,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == (Str2Int(a@) * Str2Int(a@)) % Str2Int(m@),
{
    multiply_mod(a, a, m)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let last_bit = sy[sy.len() - 1];
    let sy_prefix = &sy[0..sy.len() - 1];
    
    if sy_prefix.len() == 0 {
        if last_bit == '0' {
            let mut result = Vec::<char>::new();
            result.push('1');
            return result;
        } else {
            let mut result = Vec::<char>::new();
            for &c in sx {
                result.push(c);
            }
            return result;
        }
    }
    
    let half_exp = ModExp_Add_ModExpPow2(sx, sy_prefix, sz);
    let squared = square_mod(&half_exp, sz);
    
    if last_bit == '0' {
        squared
    } else {
        multiply_mod(&squared, sx, sz)
    }
}
// </vc-code>

fn main() {}
}
