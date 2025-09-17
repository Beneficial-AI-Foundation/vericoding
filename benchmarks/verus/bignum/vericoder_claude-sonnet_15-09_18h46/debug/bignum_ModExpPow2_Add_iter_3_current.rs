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
{    /* code modified by LLM (iteration 3): Fixed type mismatches by using nat literals */
    let mut result = Vec::new();
    let mut carry = 0;
    let mut i = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            ValidBitString(result@),
            carry == 0 || carry == 1,
            i <= max_len
        decreases max_len - i + carry
    {
        let bit1 = if i < s1.len() { if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < s2.len() { if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        result.push(result_bit);
        carry = sum / 2;
        i = i + 1;
    }
    
    let mut final_result = Vec::new();
    let mut j = result.len();
    while j > 0
        invariant
            ValidBitString(final_result@),
            j <= result.len()
        decreases j
    {
        j = j - 1;
        final_result.push(result[j]);
    }
    
    if final_result.len() == 0 {
        final_result.push('0');
    }
    
    final_result
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
{    /* code modified by LLM (iteration 3): Fixed type errors by removing improper int casts */
    if n == 0 {
        if Str2Int(sy@) == 1nat {
            let mut result = Vec::new();
            result.push('1');
            return result;
        } else {
            let mut result = Vec::new();
            result.push('1');
            return result;
        }
    }
    
    if Str2Int(sy@) == 0nat {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut half_y = Vec::new();
    let mut i = 0;
    while i < sy.len() - 1
        invariant
            ValidBitString(half_y@),
            i <= sy.len() - 1
        decreases sy.len() - 1 - i
    {
        half_y.push(sy[i + 1]);
        i = i + 1;
    }
    
    let sub_result = ModExpPow2(sx, &half_y, n - 1, sz);
    let squared = ModExpPow2(&sub_result, &half_y, n - 1, sz);
    
    if sy[0] == '1' {
        let temp = ModExpPow2(sx, &['1'], 0, sz);
        let mut final_result = Vec::new();
        final_result.push('1');
        final_result
    } else {
        squared
    }
}
// </vc-code>

fn main() {}
}


