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
exec fn char_to_digit(c: char) -> nat
    requires c == '0' || c == '1'
    ensures c == '0' ==> char_to_digit(c) == 0nat,
            c == '1' ==> char_to_digit(c) == 1nat
{
    if c == '1' { 1nat } else { 0nat }
}

exec fn digit_to_char(d: nat) -> char
    requires d == 0 || d == 1
    ensures d == 0 ==> digit_to_char(d) == '0',
            d == 1 ==> digit_to_char(d) == '1'
{
    if d == 1 { '1' } else { '0' }
}

exec fn int_to_bitstring(mut n: nat) -> Vec<char>
    ensures ValidBitString(int_to_bitstring(n)@),
            n > 0 ==> Str2Int(int_to_bitstring(n)@) == n
{
    if n == 0 {
        return vec!['0'];
    }
    let mut result = Vec::new();
    while n > 0
        invariant ValidBitString(result@)
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    result.reverse();
    result
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
    if sy.len() == 1 && sy[0] == '0' {
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        let x_mod_z = Str2Int(sx@) % Str2Int(sz@);
        return int_to_bitstring(x_mod_z);
    }
    
    let y_div_2 = sy.len() - 1;
    let mut sy_half = Vec::new();
    let mut i = 0;
    while i < y_div_2
        invariant i <= y_div_2,
                  sy_half.len() == i,
                  ValidBitString(sy_half@)
    {
        sy_half.push(sy[i]);
        i = i + 1;
    }
    
    if sy_half.len() == 0 {
        sy_half.push('0');
    }
    
    let temp = ModExp_Add_ModExpPow2(sx, sy_half.as_slice(), sz);
    let temp_squared = (Str2Int(temp@) * Str2Int(temp@)) % Str2Int(sz@);
    
    if sy[sy.len() - 1] == '0' {
        return int_to_bitstring(temp_squared);
    } else {
        let final_result = (temp_squared * Str2Int(sx@)) % Str2Int(sz@);
        return int_to_bitstring(final_result);
    }
}
// </vc-code>

fn main() {}
}
