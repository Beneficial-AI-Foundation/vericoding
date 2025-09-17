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
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    for c in dividend.iter() {
        remainder.push(*c);
    }
    
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);
    
    if dividend_val == 0 {
        quotient.push('0');
        remainder = Vec::<char>::new();
        remainder.push('0');
        return (quotient, remainder);
    }
    
    let q = dividend_val / divisor_val;
    let r = dividend_val % divisor_val;
    
    quotient = Vec::<char>::new();
    remainder = Vec::<char>::new();
    
    if q == 0 {
        quotient.push('0');
    } else {
        let mut temp_q = q;
        let mut q_chars = Vec::<char>::new();
        while temp_q > 0 {
            if temp_q % 2 == 1 {
                q_chars.push('1');
            } else {
                q_chars.push('0');
            }
            temp_q = temp_q / 2;
        }
        for i in 0..q_chars.len() {
            quotient.push(q_chars[q_chars.len() - 1 - i]);
        }
    }
    
    if r == 0 {
        remainder.push('0');
    } else {
        let mut temp_r = r;
        let mut r_chars = Vec::<char>::new();
        while temp_r > 0 {
            if temp_r % 2 == 1 {
                r_chars.push('1');
            } else {
                r_chars.push('0');
            }
            temp_r = temp_r / 2;
        }
        for i in 0..r_chars.len() {
            remainder.push(r_chars[r_chars.len() - 1 - i]);
        }
    }
    
    proof {
        assert(ValidBitString(quotient@));
        assert(ValidBitString(remainder@));
        assert(Str2Int(quotient@) == Str2Int(dividend@) / Str2Int(divisor@));
        assert(Str2Int(remainder@) == Str2Int(dividend@) % Str2Int(divisor@));
    }
    
    (quotient, remainder)
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
        let mut result = Vec::<char>::new();
        result.push('1');
        proof {
            assert(Str2Int(sy@) == 0 || Str2Int(sy@) == 1);
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == 1);
            assert(Str2Int(result@) == 1);
        }
        return result;
    }
    
    if Str2Int(sy@) == 0 {
        let mut result = Vec::<char>::new();
        result.push('1');
        proof {
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(Str2Int(result@) == 1);
        }
        return result;
    }
    
    let mut sy_half = Vec::<char>::new();
    for i in 0..(sy.len() - 1) {
        sy_half.push(sy[i]);
    }
    
    if sy_half.is_empty() {
        sy_half.push('0');
    }
    
    let temp_result = ModExpPow2(sx, &sy_half, n - 1, sz);
    let squared = ModExpPow2(&temp_result, &sy_half, n - 1, sz);
    
    let result = if sy[sy.len() - 1] == '1' {
        let (prod_quot, prod_rem) = DivMod(&squared, sz);
        let sx_mod = DivMod(sx, sz).1;
        let (final_quot, final_rem) = DivMod(&sx_mod, sz);
        final_rem
    } else {
        squared
    };
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    result
}
// </vc-code>

fn main() {}
}


