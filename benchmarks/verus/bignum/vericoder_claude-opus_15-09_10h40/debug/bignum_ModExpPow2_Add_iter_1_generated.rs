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
    let mut carry = 0u8;
    let mut result = Vec::new();
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            0 <= i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            Str2Int(result@) == (Str2Int(s1@.subrange(0, i.min(s1.len() as int))) + Str2Int(s2@.subrange(0, i.min(s2.len() as int))) + carry as nat) % Exp_int(2, i as nat),
            (Str2Int(s1@.subrange(0, i.min(s1.len() as int))) + Str2Int(s2@.subrange(0, i.min(s2.len() as int))) + carry as nat) / Exp_int(2, i as nat) <= 1
    {
        let bit1 = if i < s1.len() { if s1[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let bit2 = if i < s2.len() { if s2[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let sum = bit1 + bit2 + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i = i + 1;
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
        if sy[0] == '1' {
            let mut result = Vec::new();
            result.push('1');
            return result;
        } else {
            let mut result = Vec::new();
            result.push('0');
            return result;
        }
    }
    let half_power = &sy[0..sy.len()-1];
    let half_result = ModExpPow2(sx, half_power, n - 1, sz);
    let squared = ModExpPow2(&half_result, &half_power, n - 1, sz);
    if sy[sy.len()-1] == '1' {
        let multiplied = ModExpPow2(sx, &['1'], 0, sz);
        let final_result = ModExpPow2(&squared, &multiplied, 0, sz);
        return final_result;
    } else {
        return squared;
    }
}
// </vc-code>

fn main() {}
}


