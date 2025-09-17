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
proof fn lemma_div_mod_subtraction(dividend: nat, divisor: nat) 
    requires divisor > 0
    ensures dividend / divisor == ((dividend - (dividend % divisor)) as int) / (divisor as int),
        dividend % divisor == dividend % divisor
{
}

proof fn lemma_div_mod_identity(dividend: nat, divisor: nat)
    requires divisor > 0
    ensures dividend == divisor * (dividend / divisor) + (dividend % divisor)
{
}

proof fn lemma_str2int_nonempty(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 
        (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
{
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_valid_bitstring_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len() as int
    ensures ValidBitString(s.subrange(start, end))
{
}

proof fn lemma_valid_bitstring_append(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures ValidBitString(s1 + s2)
{
}

fn compare_and_subtract(remainder: &mut Vec<char>, divisor: &[char]) -> (result: bool)
    requires ValidBitString(remainder@), ValidBitString(divisor@), Str2Int(divisor@) > 0
    ensures ValidBitString(remainder@), result ==> Str2Int(old(remainder)@) >= Str2Int(divisor@),
        !result ==> Str2Int(old(remainder)@) < Str2Int(divisor@),
        if result { Str2Int(remainder@) == Str2Int(old(remainder)@) - Str2Int(divisor@) } else { Str2Int(remainder@) == Str2Int(old(remainder)@) }
{
    let rem_val = Str2Int(remainder@);
    let div_val = Str2Int(divisor@);
    
    if rem_val >= div_val {
        proof {
            lemma_div_mod_subtraction(rem_val, div_val);
        }
        let new_val = rem_val - div_val;
        let mut new_bits = Vec::new();
        let mut temp = new_val as int;
        
        while temp > 0
            invariant ValidBitString(new_bits@), Str2Int(new_bits@) == temp as nat
            decreases temp
        {
            if temp % 2 == 1 {
                new_bits.push('1');
            } else {
                new_bits.push('0');
            }
            temp = temp / 2;
        }
        
        new_bits.reverse();
        *remainder = new_bits;
        true
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed type conversion error */
{
    let mut quotient_bits = Vec::new();
    let mut remainder_bits = Vec::new();
    
    let mut current_dividend = dividend.to_vec();
    
    for i in 0..dividend.len()
        invariant ValidBitString(current_dividend@), ValidBitString(quotient_bits@), ValidBitString(remainder_bits@),
            Str2Int(current_dividend@) == Str2Int(dividend@) - Str2Int(quotient_bits@) * Str2Int(divisor@) * (2.pow((dividend.len() - i) as u32) as nat),
            Str2Int(remainder_bits@) == 0
    {
        remainder_bits.push(current_dividend[i]);
        
        proof {
            lemma_valid_bitstring_append(remainder_bits@, Seq::empty());
        }
        
        let result = compare_and_subtract(&mut remainder_bits, divisor);
        
        if result {
            quotient_bits.push('1');
        } else {
            quotient_bits.push('0');
        }
        
        proof {
            lemma_div_mod_identity(Str2Int(current_dividend@), Str2Int(divisor@));
        }
    }
    
    (quotient_bits, remainder_bits)
}
// </vc-code>

fn main() {}
}

