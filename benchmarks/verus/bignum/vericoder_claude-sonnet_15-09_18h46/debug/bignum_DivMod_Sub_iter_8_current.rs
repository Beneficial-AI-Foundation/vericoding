use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helpers modified by LLM (iteration 8): fixed type mismatches and removed int from subtract_bit_strings */
spec fn is_zero(s: Seq<char>) -> bool {
    Str2Int(s) == 0
}

spec fn compare_bit_strings(a: Seq<char>, b: Seq<char>) -> int
    requires ValidBitString(a), ValidBitString(b)
{
    if Str2Int(a) < Str2Int(b) { -1 }
    else if Str2Int(a) == Str2Int(b) { 0 }
    else { 1 }
}

spec fn int_to_bit_string(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let rest = int_to_bit_string(n / 2);
        let last_bit = if n % 2 == 0 { '0' } else { '1' };
        rest.push(last_bit)
    }
}

exec fn nat_to_bit_string(n: usize) -> (res: Vec<char>)
    ensures ValidBitString(res@)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::<char>::new();
        let mut temp = n;
        while temp > 0 {
            if temp % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            temp = temp / 2;
        }
        result.reverse();
        result
    }
}

exec fn bit_string_compare(a: &[char], b: &[char]) -> (res: i32)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures res == compare_bit_strings(a@, b@)
{
    let a_val = Str2Int(a@);
    let b_val = Str2Int(b@);
    if a_val < b_val {
        -1
    } else if a_val == b_val {
        0
    } else {
        1
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): fixed type errors and simplified implementation */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    for c in dividend {
        remainder.push(*c);
    }
    
    if Str2Int(dividend@) < Str2Int(divisor@) {
        quotient.push('0');
        return (quotient, remainder);
    }
    
    let mut current = Vec::<char>::new();
    let mut q_bits = Vec::<char>::new();
    
    for i in 0..dividend.len() {
        current.push(dividend[i]);
        
        if Str2Int(current@) >= Str2Int(divisor@) {
            q_bits.push('1');
            let diff_nat = Str2Int(current@) - Str2Int(divisor@);
            current = nat_to_bit_string(diff_nat as usize);
        } else {
            q_bits.push('0');
        }
    }
    
    if q_bits.len() == 0 {
        q_bits.push('0');
    }
    
    (q_bits, current)
}
// </vc-code>

fn main() {}
}

