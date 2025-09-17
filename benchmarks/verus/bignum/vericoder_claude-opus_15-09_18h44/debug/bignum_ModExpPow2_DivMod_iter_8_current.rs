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
{
/* code modified by LLM (iteration 8): Fixed type errors with nat literals */
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    let dividend_int = Str2Int(dividend@);
    let divisor_int = Str2Int(divisor@);
    
    let q = dividend_int / divisor_int;
    let r = dividend_int % divisor_int;
    
    // Convert quotient to binary string
    let mut q_temp = q;
    if q_temp == 0nat {
        quotient.push('0');
    } else {
        let mut temp_vec = Vec::new();
        while q_temp > 0nat {
            if q_temp % 2nat == 0nat {
                temp_vec.push('0');
            } else {
                temp_vec.push('1');
            }
            q_temp = q_temp / 2nat;
        }
        // Reverse to get correct order
        let mut i = temp_vec.len();
        while i > 0 {
            i = i - 1;
            quotient.push(temp_vec[i]);
        }
    }
    
    // Convert remainder to binary string
    let mut r_temp = r;
    if r_temp == 0nat {
        remainder.push('0');
    } else {
        let mut temp_vec = Vec::new();
        while r_temp > 0nat {
            if r_temp % 2nat == 0nat {
                temp_vec.push('0');
            } else {
                temp_vec.push('1');
            }
            r_temp = r_temp / 2nat;
        }
        // Reverse to get correct order
        let mut i = temp_vec.len();
        while i > 0 {
            i = i - 1;
            remainder.push(temp_vec[i]);
        }
    }
    
    return (quotient, remainder);
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
/* code modified by LLM (iteration 8): Fixed type errors with int/nat literals */
    if n == 0int {
        // sy is either "10" (2^0 = 1) or "0"
        if sy.len() >= 1 && sy[0] == '0' {
            // sy represents 0, so result is 1 % z
            let one_str = vec!['1'];
            let (_, remainder) = DivMod(&one_str, sz);
            return remainder;
        } else {
            // sy represents 1 (2^0), so result is x % z
            let (_, remainder) = DivMod(sx, sz);
            return remainder;
        }
    } else {
        // Recursive case: compute x^(y/2) mod z
        let mut y_half = Vec::new();
        
        // Shift sy right by 1 bit (divide by 2)
        if sy.len() > 1 {
            for i in 0..(sy.len() - 1) {
                y_half.push(sy[i]);
            }
        } else {
            y_half.push('0');
        }
        
        let half_result = ModExpPow2(sx, &y_half, n - 1int, sz);
        
        // Square the half_result
        let mut squared = Vec::new();
        let half_int = Str2Int(half_result@);
        let squared_int = (half_int * half_int) % Str2Int(sz@);
        
        // Convert squared_int to binary
        let mut temp = squared_int;
        if temp == 0nat {
            squared.push('0');
        } else {
            let mut temp_vec = Vec::new();
            while temp > 0nat {
                if temp % 2nat == 0nat {
                    temp_vec.push('0');
                } else {
                    temp_vec.push('1');
                }
                temp = temp / 2nat;
            }
            let mut i = temp_vec.len();
            while i > 0 {
                i = i - 1;
                squared.push(temp_vec[i]);
            }
        }
        
        return squared;
    }
}
// </vc-code>

fn main() {}
}


