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
/* helper modified by LLM (iteration 6): Fixed function signature and placement */
exec fn add_bit_strings(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    let mut result = Vec::new();
    let mut carry = 0;
    let mut i = 0;
    
    while i <= max_len
        invariant
            i <= max_len + 1,
            ValidBitString(result@)
    {
        let digit1 = if i < s1.len() { if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let digit2 = if i < s2.len() { if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        
        let sum = digit1 + digit2 + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        
        i += 1;
        if i > max_len && carry == 0 {
            break;
        }
    }
    
    result.reverse();
    remove_leading_zeros(&result)
}

exec fn remove_leading_zeros(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@)
{
    let mut start = 0;
    while start < s.len() && s[start] == '0'
        invariant
            start <= s.len()
    {
        start += 1;
    }
    
    if start == s.len() {
        vec!['0']
    } else {
        s[start..].to_vec()
    }
}

exec fn simple_mod(dividend: &[char], divisor: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(dividend@),
        ValidBitString(divisor@),
        Str2Int(divisor@) > 0
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(dividend@) % Str2Int(divisor@)
{
    if compare_bit_strings(dividend, divisor) < 0 {
        return dividend.to_vec();
    }
    
    let mut result = dividend.to_vec();
    
    while compare_bit_strings(&result, divisor) >= 0
        invariant
            ValidBitString(result@)
    {
        result = subtract_bit_strings(&result, divisor);
    }
    
    result
}

exec fn compare_bit_strings(s1: &[char], s2: &[char]) -> (res: i32)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@)
    ensures
        (res < 0) == (Str2Int(s1@) < Str2Int(s2@)),
        (res == 0) == (Str2Int(s1@) == Str2Int(s2@)),
        (res > 0) == (Str2Int(s1@) > Str2Int(s2@))
{
    if s1.len() < s2.len() { return -1; }
    if s1.len() > s2.len() { return 1; }
    
    let mut i = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            s1.len() == s2.len()
    {
        if s1[i] < s2[i] { return -1; }
        if s1[i] > s2[i] { return 1; }
        i += 1;
    }
    
    0
}

exec fn subtract_bit_strings(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
        Str2Int(s1@) >= Str2Int(s2@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
{
    let mut result = vec!['0'; s1.len()];
    let mut borrow = 0;
    let mut i = s1.len();
    
    while i > 0
        invariant
            i <= s1.len(),
            result.len() == s1.len(),
            ValidBitString(result@)
    {
        i -= 1;
        let digit1 = if s1[i] == '1' { 1 } else { 0 };
        let digit2 = if i < s2.len() && s2[i] == '1' { 1 } else { 0 };
        
        let diff = digit1 - digit2 - borrow;
        
        if diff >= 0 {
            result[i] = if diff == 1 { '1' } else { '0' };
            borrow = 0;
        } else {
            result[i] = '1';
            borrow = 1;
        }
    }
    
    remove_leading_zeros(&result)
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
    /* code modified by LLM (iteration 6): Fixed Mul implementation using grade school multiplication */
    if s1.len() == 0 || s2.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    
    let mut i = 0;
    while i < s2.len()
        invariant
            i <= s2.len(),
            ValidBitString(result@)
    {
        if s2[s2.len() - 1 - i] == '1' {
            let mut shifted_s1 = s1.to_vec();
            let mut j = 0;
            while j < i
                invariant
                    j <= i,
                    ValidBitString(shifted_s1@)
            {
                shifted_s1.push('0');
                j += 1;
            }
            result = add_bit_strings(&result, &shifted_s1);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


