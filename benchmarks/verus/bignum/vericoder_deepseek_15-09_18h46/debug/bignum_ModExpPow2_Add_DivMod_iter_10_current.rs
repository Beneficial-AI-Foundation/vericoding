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
fn bitwise_add(a: char, b: char, carry: char) -> (sum: char, carry_out: char) {
    let a_val = if a == '1' { 1 } else { 0 };
    let b_val = if b == '1' { 1 } else { 0 };
    let carry_val = if carry == '1' { 1 } else { 0 };
    let total = a_val + b_val + carry_val;
    if total == 0 { ('0', '0') }
    else if total == 1 { ('1', '0') }
    else if total == 2 { ('0', '1') }
    else { ('1', '1') }
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
/* code modified by LLM (iteration 10): Fixed Add implementation */
{
    let mut result = Vec::<char>::new();
    let mut carry = '0';
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i && i <= max_len,
            ValidBitString(result@),
            carry == '0' || carry == '1',
            Str2Int(result@) + Exp_int(2, i as nat) * (if carry == '1' { 1 } else { 0 })
                == Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int))
    {
        let c1 = if i < s1.len() { s1[i] } else { '0' };
        let c2 = if i < s2.len() { s2[i] } else { '0' };
        let (sum, new_carry) = bitwise_add(c1, c2, carry);
        result.push(sum);
        carry = new_carry;
        i += 1;
    }
    
    if carry == '1' {
        result.push('1');
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
/* code modified by LLM (iteration 10): Fixed DivMod implementation */
{
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    let mut current_val = 0;
    let divisor_val = Str2Int(divisor@);
    
    let mut i = 0;
    while i < dividend.len()
        invariant
            0 <= i && i <= dividend.len(),
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(remainder@) + Exp_int(2, remainder.len() as nat) * current_val
                == Str2Int(dividend@.subrange(0, i as int)) % divisor_val,
            Str2Int(quotient@) == Str2Int(dividend@.subrange(0, i as int)) / divisor_val
    {
        current_val = current_val * 2 + (if dividend[i] == '1' { 1 } else { 0 });
        if current_val >= divisor_val {
            quotient.push('1');
            current_val -= divisor_val;
        } else {
            quotient.push('0');
        }
        i += 1;
    }
    
    while remainder.len() < 32 {
        if current_val == 0 {
            remainder.push('0');
        } else {
            remainder.push(if current_val % 2 == 1 { '1' } else { '0' });
            current_val /= 2;
        }
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


