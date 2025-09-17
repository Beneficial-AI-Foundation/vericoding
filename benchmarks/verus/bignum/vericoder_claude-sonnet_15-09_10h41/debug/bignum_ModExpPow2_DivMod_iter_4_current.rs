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
/* helper modified by LLM (iteration 4): Added helper to convert nat to bit string */
fn nat_to_bit_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
            Str2Int(result@) == n
{
    if n == 0nat {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let mut temp_n = n;
    let mut chars = Vec::<char>::new();
    
    while temp_n > 0nat
        invariant temp_n >= 0nat
    {
        if temp_n % 2nat == 1nat {
            chars.push('1');
        } else {
            chars.push('0');
        }
        temp_n = temp_n / 2nat;
    }
    
    let mut result = Vec::<char>::new();
    for i in 0..chars.len() {
        result.push(chars[chars.len() - 1 - i]);
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
    /* code modified by LLM (iteration 4): Fixed type mismatches with nat literals */
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);
    
    if dividend_val == 0nat {
        let mut quotient = Vec::<char>::new();
        quotient.push('0');
        let mut remainder = Vec::<char>::new();
        remainder.push('0');
        return (quotient, remainder);
    }
    
    let q = dividend_val / divisor_val;
    let r = dividend_val % divisor_val;
    
    let quotient = nat_to_bit_string(q);
    let remainder = nat_to_bit_string(r);
    
    proof {
        assert(ValidBitString(quotient@));
        assert(ValidBitString(remainder@));
        assert(Str2Int(quotient@) == Str2Int(dividend@) / Str2Int(divisor@));
        assert(Str2Int(remainder@) == Str2Int(dividend@) % Str2Int(divisor@));
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


