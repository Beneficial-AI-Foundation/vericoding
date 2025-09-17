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
    let mut carry = 0;
    let mut i = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 1,
            i <= max_len
    {
        let bit1 = if i < s1.len() && s1[s1.len() - 1 - i] == '1' { 1 } else { 0 };
        let bit2 = if i < s2.len() && s2[s2.len() - 1 - i] == '1' { 1 } else { 0 };
        let sum = bit1 + bit2 + carry;
        
        if sum % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        
        carry = sum / 2;
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
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy@.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let last_bit = sy[sy.len() - 1];
    let sy_prefix = &sy[0..sy.len()-1];
    
    if last_bit == '0' {
        let temp = ModExp(sx, sy_prefix, sz);
        let squared = ModMul(&temp, &temp, sz);
        return squared;
    } else {
        let temp = ModExp(sx, sy_prefix, sz);
        let squared = ModMul(&temp, &temp, sz);
        let result = ModMul(&squared, sx, sz);
        return result;
    }
}
// </vc-code>

fn main() {}
}


