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
fn bit_adder(a: char, b: char, carry_in: char) -> (sum: char, carry_out: char)
    ensures
        a == '0' || a == '1',
        b == '0' || b == '1',
        carry_in == '0' || carry_in == '1',
        sum == '0' || sum == '1',
        carry_out == '0' || carry_out == '1',
        (if a == '1' { 1 } else { 0 }) + (if b == '1' { 1 } else { 0 }) + (if carry_in == '1' { 1 } else { 0 })
            == (if sum == '1' { 1 } else { 0 }) + 2 * (if carry_out == '1' { 1 } else { 0 })
{
    let a_val = if a == '1' { 1 } else { 0 };
    let b_val = if b == '1' { 1 } else { 0 };
    let carry_in_val = if carry_in == '1' { 1 } else { 0 };
    let total = a_val + b_val + carry_in_val;
    if total % 2 == 1 { ('1', if total >= 2 { '1' } else { '0' }) } else { ('0', if total >= 2 { '1' } else { '0' }) }
}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::<char>::new();
    let mut i = s1.len() as int - 1;
    let mut j = s2.len() as int - 1;
    let mut carry = '0';
    
    while i >= 0 || j >= 0 || carry == '1'
        invariant
            ValidBitString(res@),
            Str2Int(res@) + Exp_int(2, (res.len() as nat)) * (if carry == '1' { 1 } else { 0 }) 
                == Str2Int(s1@.subrange(i+1, s1.len() as int)) + Str2Int(s2@.subrange(j+1, s2.len() as int)),
            res.len() as int <= s1.len() + s2.len() + 1
        decreases
            if i >= 0 { i } else { -1 } + if j >= 0 { j } else { -1 }
    {
        let a = if i >= 0 { s1[i] } else { '0' };
        let b = if j >= 0 { s2[j] } else { '0' };
        let (sum, new_carry) = bit_adder(a, b, carry);
        res.push(sum);
        carry = new_carry;
        if i >= 0 { i -= 1; }
        if j >= 0 { j -= 1; }
    }
    
    res.reverse();
    res
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
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    // Copy dividend to remainder initially
    for i in 0..dividend.len() as int {
        remainder.push(dividend[i]);
    }
    
    let divisor_val = Str2Int(divisor@);
    let mut current_val = 0;
    let mut temp_quotient = Vec::<char>::new();
    
    for i in 0..remainder.len() as int
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(remainder@) + divisor_val * Str2Int(quotient@) * Exp_int(2, (remainder.len() as int - i) as nat) 
                == Str2Int(dividend@),
            Str2Int(remainder@) < divisor_val * Exp_int(2, (remainder.len() as int - i) as nat)
        decreases
            remainder.len() as int - i
    {
        current_val = current_val * 2 + (if remainder[i] == '1' { 1 } else { 0 });
        
        if current_val >= divisor_val {
            current_val -= divisor_val;
            quotient.push('1');
        } else {
            quotient.push('0');
        }
        
        remainder[i] = if current_val % 2 == 1 { '1' } else { '0' };
        current_val /= 2;
    }
    
    // Remove leading zeros from quotient
    while quotient.len() > 0 && quotient[0] == '0' {
        quotient.remove(0);
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    // Remove leading zeros from remainder
    while remainder.len() > 0 && remainder[0] == '0' {
        remainder.remove(0);
    }
    
    if remainder.len() == 0 {
        remainder.push('0');
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


