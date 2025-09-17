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
proof fn lemma_div_remainder(a: nat, b: nat)
    requires b > 0
    ensures a % b < b
{
    // This is a fundamental property of modulo operation
}

fn int_to_bitstring(mut num: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == num
{
    let mut bits = Vec::new();
    if num == 0 {
        bits.push('0');
    } else {
        while num > 0
            invariant ValidBitString(bits@)
            decreases num
        {
            if num % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            num = num / 2;
        }
        bits = bits.into_iter().rev().collect();
    }
    bits
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
    /* code modified by LLM (iteration 3): fix compilation error by adding proper function body braces */
    let mut dividend_vec = dividend.to_vec();
    let mut quotient: Vec<char> = Vec::new();
    let mut remainder: Vec<char> = Vec::new();
    
    let mut current: Vec<char> = Vec::new();
    let divisor_int = Str2Int(divisor@);
    
    let mut i = 0;
    while i < dividend_vec.len()
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            ValidBitString(current@),
            current@.len() <= divisor@.len(),
            Str2Int(dividend@) == (Str2Int(quotient@) * divisor_int + Str2Int(current@)) * Exp_int(2, (dividend_vec.len() - i) as nat) + Str2Int(dividend_vec.subrange(i as int, dividend_vec.len() as int)),
            i <= dividend_vec.len()
        decreases dividend_vec.len() - i
    {
        current.push(dividend_vec[i]);
        if Str2Int(current@) >= divisor_int {
            quotient.push('1');
            let current_val = Str2Int(current@);
            proof {
                lemma_div_remainder(current_val, divisor_int);
            }
            let new_remainder = current_val % divisor_int;
            current = int_to_bitstring(new_remainder);
        } else {
            quotient.push('0');
        }
        i += 1;
    }
    
    if Str2Int(current@) < divisor_int {
        remainder = current;
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


