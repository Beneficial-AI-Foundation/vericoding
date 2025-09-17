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
/* helper modified by LLM (iteration 4): Added multiply_mod and bit manipulation helper functions */
exec fn multiply_mod(a: &Vec<char>, b: &Vec<char>, modulus: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@), ValidBitString(modulus@), Str2Int(modulus@) > 0
    ensures ValidBitString(res@),
        Str2Int(res@) == (Str2Int(a@) * Str2Int(b@)) % Str2Int(modulus@)
{
    let product = multiply_bits(a, b);
    let (_, remainder) = DivMod(&product, modulus);
    remainder
}

exec fn multiply_bits(a: &Vec<char>, b: &Vec<char>) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) * Str2Int(b@)
{
    if a@.len() == 0 || b@.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    let mut temp_a = a.clone();
    
    for i in 0..b.len()
        invariant
            ValidBitString(result@),
            ValidBitString(temp_a@)
    {
        if b[b.len() - 1 - i] == '1' {
            result = add_bits(&result, &temp_a);
        }
        temp_a = shift_left(&temp_a);
    }
    
    result
}

exec fn add_bits(a: &Vec<char>, b: &Vec<char>) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) + Str2Int(b@)
{
    let mut result = Vec::new();
    let mut carry = false;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    for i in 0..max_len + 1
        invariant ValidBitString(result@)
    {
        let a_bit = if i < a.len() { a[a.len() - 1 - i] == '1' } else { false };
        let b_bit = if i < b.len() { b[b.len() - 1 - i] == '1' } else { false };
        
        let sum = (a_bit as u8) + (b_bit as u8) + (carry as u8);
        result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum >= 2;
    }
    
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}

exec fn shift_left(a: &Vec<char>) -> (res: Vec<char>)
    requires ValidBitString(a@)
    ensures ValidBitString(res@),
        Str2Int(res@) == 2 * Str2Int(a@)
{
    let mut result = a.clone();
    result.push('0');
    result
}

exec fn divide_by_two(a: &Vec<char>) -> (res: Vec<char>)
    requires ValidBitString(a@)
    ensures ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) / 2
{
    if a.len() <= 1 {
        return vec!['0'];
    }
    
    let mut result = Vec::new();
    for i in 0..a.len() - 1 {
        result.push(a[i]);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}

exec fn subtract_bits(a: &Vec<char>, b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@),
        Str2Int(a@) >= Str2Int(b@)
    ensures ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) - Str2Int(b@)
{
    let mut result = a.clone();
    let mut borrow = false;
    
    for i in 0..result.len()
        invariant ValidBitString(result@)
    {
        let b_bit = if i < b.len() { b[b.len() - 1 - i] == '1' } else { false };
        let mut a_bit = result[result.len() - 1 - i] == '1';
        
        if borrow {
            if a_bit {
                a_bit = false;
                borrow = false;
            } else {
                a_bit = true;
                borrow = true;
            }
        }
        
        if b_bit {
            if a_bit {
                result[result.len() - 1 - i] = '0';
            } else {
                result[result.len() - 1 - i] = '1';
                borrow = true;
            }
        } else {
            result[result.len() - 1 - i] = if a_bit { '1' } else { '0' };
        }
    }
    
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    
    result
}

exec fn add_one(a: &Vec<char>) -> (res: Vec<char>)
    requires ValidBitString(a@)
    ensures ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) + 1
{
    let one = vec!['1'];
    add_bits(a, &one)
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
    /* code modified by LLM (iteration 4): Fixed to use correct parameter names dividend and divisor */
    if dividend@.len() == 0 {
        return (vec!['0'], vec!['0']);
    }
    
    if Str2Int(dividend@) < Str2Int(divisor@) {
        return (vec!['0'], dividend.to_vec());
    }
    
    let mut quotient = vec!['0'];
    let mut remainder = dividend.to_vec();
    
    while Str2Int(remainder@) >= Str2Int(divisor@)
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            ValidBitString(divisor@),
            Str2Int(divisor@) > 0
    {
        remainder = subtract_bits(&remainder, divisor);
        quotient = add_one(&quotient);
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


