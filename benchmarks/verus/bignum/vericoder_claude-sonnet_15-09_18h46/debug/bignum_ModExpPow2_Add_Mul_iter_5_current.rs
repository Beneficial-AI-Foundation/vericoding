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
    /* code modified by LLM (iteration 5): Fixed type mismatches with proper casting */
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i <= max_len
        invariant
            ValidBitString(result@),
            carry <= 1,
            i <= max_len + 1
    {
        let bit1 = if i < s1.len() && s1.len() > 0 {
            if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let bit2 = if i < s2.len() && s2.len() > 0 {
            if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(result_bit);
        
        if i >= max_len && carry == 0 {
            break;
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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches with proper casting */
    if s1.len() == 0 || s2.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i = 0;
    while i < s2.len()
        invariant
            ValidBitString(result@),
            i <= s2.len()
    {
        if s2[s2.len() - 1 - i] == '1' {
            let mut shifted_s1 = Vec::<char>::new();
            for j in 0..s1.len() {
                shifted_s1.push(s1[j]);
            }
            for _ in 0..i {
                shifted_s1.push('0');
            }
            result = Add(&result, &shifted_s1);
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
    /* code modified by LLM (iteration 5): Fixed type mismatches with proper casting */
    if n == 0int {
        if sy.len() > 0 && sy[0] == '1' {
            let mut result = Vec::<char>::new();
            result.push('1');
            return result;
        } else {
            let mut result = Vec::<char>::new();
            result.push('1');
            return result;
        }
    }
    
    if Str2Int(sy@) == 0nat {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let mut half_y = Vec::<char>::new();
    for i in 0..sy.len()-1 {
        half_y.push(sy[i]);
    }
    
    let half_result = ModExpPow2(sx, &half_y, n - 1int, sz);
    let squared = Mul(&half_result, &half_result);
    
    let mut mod_result = Vec::<char>::new();
    mod_result.push('0');
    
    if sy[sy.len() - 1] == '1' {
        let temp = Mul(&squared, sx);
        mod_result = temp;
    } else {
        mod_result = squared;
    }
    
    mod_result
}
// </vc-code>

fn main() {}
}
