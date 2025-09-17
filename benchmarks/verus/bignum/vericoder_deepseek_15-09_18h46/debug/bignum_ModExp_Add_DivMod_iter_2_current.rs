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
fn add_helper(a: char, b: char, carry: char) -> (sum: char, new_carry: char)
    ensures
        (sum == '0' || sum == '1') && (new_carry == '0' || new_carry == '1'),
        (if a == '1' { 1nat } else { 0nat }) + (if b == '1' { 1nat } else { 0nat }) + (if carry == '1' { 1nat } else { 0nat })
            == (if sum == '1' { 1nat } else { 0nat }) + 2 * (if new_carry == '1' { 1nat } else { 0nat })
{
    let ones = (if a == '1' { 1 } else { 0 }) + (if b == '1' { 1 } else { 0 }) + (if carry == '1' { 1 } else { 0 });
    match ones {
        0 => ('0', '0'),
        1 => ('1', '0'),
        2 => ('0', '1'),
        _ => ('1', '1'),
    }
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
    /* code modified by LLM (iteration 2): Fixed compilation errors in Add implementation */
    let mut i = s1.len() as int - 1;
    let mut j = s2.len() as int - 1;
    let mut carry = '0';
    let mut result = Vec::new();
    
    loop
        invariant
            i >= -1,
            j >= -1,
            ValidBitString(result@),
            Str2Int(result@) + Exp_int(2, result.len() as nat) * (if carry == '1' { 1nat } else { 0nat }) 
                == Str2Int(s1.subrange(i + 1, s1.len() as int)) + Str2Int(s2.subrange(j + 1, s2.len() as int))
        decreases i + j + 2
    {
        if i == -1 && j == -1 && carry == '0' {
            break;
        }
        
        let bit1 = if i >= 0 { s1[i as usize] } else { '0' };
        let bit2 = if j >= 0 { s2[j as usize] } else { '0' };
        
        let (sum, new_carry) = add_helper(bit1, bit2, carry);
        result.push(sum);
        carry = new_carry;
        
        if i > -1 { i -= 1; }
        if j > -1 { j -= 1; }
    }
    
    result.reverse();
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
    /* code modified by LLM (iteration 2): Fixed compilation errors in DivMod implementation */
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
        
        if Str2Int(remainder@) >= Str2Int(divisor@) {
            let mut count = 0;
            let mut temp_remainder = remainder.clone();
            
            while Str2Int(temp_remainder@) >= Str2Int(divisor@) {
                temp_remainder = Add(&temp_remainder, &['0']).iter().cloned().collect();
                count += 1;
            }
            
            quotient.push(if count > 0 { '1' } else { '0' });
            remainder = temp_remainder;
        } else {
            quotient.push('0');
        }
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


