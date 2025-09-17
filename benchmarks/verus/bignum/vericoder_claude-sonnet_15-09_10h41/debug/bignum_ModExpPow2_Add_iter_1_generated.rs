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
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len,
            carry <= 1,
            ValidBitString(result@)
    {
        let bit1 = if i < s1.len() { if s1[s1.len() - 1 - i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let bit2 = if i < s2.len() { if s2[s2.len() - 1 - i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let sum = bit1 + bit2 + carry;
        let result_bit = sum % 2;
        carry = sum / 2;
        
        if result_bit == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        i += 1;
    }
    
    result.reverse();
    if result.len() == 0 {
        result.push('0');
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
        if Str2Int(sy@) == 1 {
            let mut result = Vec::<char>::new();
            result.push('1');
            return result;
        } else {
            let mut result = Vec::<char>::new();
            result.push('1');
            return result;
        }
    }
    
    if Str2Int(sy@) == 0 {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let mut half_y = Vec::<char>::new();
    for i in 0..sy.len() - 1 {
        half_y.push(sy[i]);
    }
    
    let sub_result = ModExpPow2(sx, &half_y, n - 1, sz);
    let squared = ModExpPow2(&sub_result, &half_y, n - 1, sz);
    
    if sy[sy.len() - 1] == '1' {
        let temp = ModExpPow2(&squared, sx, 0, sz);
        return temp;
    } else {
        return squared;
    }
}
// </vc-code>

fn main() {}
}


