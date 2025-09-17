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

proof fn lemma_str2int_zero()
    ensures Str2Int(Seq::<char>::empty()) == 0,
{
}

proof fn lemma_str2int_push_zero(s: Seq<char>)
    requires ValidBitString(s),
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s),
{
}

proof fn lemma_str2int_push_one(s: Seq<char>)
    requires ValidBitString(s),
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1,
{
}

proof fn lemma_divmod_recursive(dividend: Seq<char>, divisor: Seq<char>)
    requires ValidBitString(dividend), ValidBitString(divisor), Str2Int(divisor) > 0,
    ensures exists |q: Seq<char>, r: Seq<char>| ValidBitString(q) && ValidBitString(r) &&
        Str2Int(q) == Str2Int(dividend) / Str2Int(divisor) &&
        Str2Int(r) == Str2Int(dividend) % Str2Int(divisor),
{
}

proof fn lemma_divmod_step(current: Seq<char>, divisor: Seq<char>, bit: char)
    requires ValidBitString(current), ValidBitString(divisor), Str2Int(divisor) > 0,
        bit == '0' || bit == '1',
    ensures exists |q: Seq<char>, r: Seq<char>| ValidBitString(q) && ValidBitString(r) &&
        Str2Int(q) == Str2Int(current.push(bit)) / Str2Int(divisor) &&
        Str2Int(r) == Str2Int(current.push(bit)) % Str2Int(divisor),
{
}

// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    let mut current = 0;
    let divisor_val = Str2Int(divisor@);
    
    proof {
        lemma_divmod_recursive(Seq::<char>::empty(), divisor@);
    }
    
    let mut i = 0;
    while i < dividend.len()
        invariant
            0 <= i && i <= dividend.len(),
            ValidBitString(quotient@) && ValidBitString(remainder@),
            Str2Int(remainder@) < divisor_val,
            Str2Int(quotient@) * divisor_val + Str2Int(remainder@) == Str2Int(dividend@.subrange(0, i)),
        decreases dividend.len() - i
    {
        let bit = dividend[i];
        remainder.push(bit);
        
        if Str2Int(remainder@) >= divisor_val {
            let rem_val = Str2Int(remainder@);
            proof {
                lemma_divmod_step(remainder@.subrange(0, remainder.len() as int - 1), divisor@, bit);
            }
            let q_digit = rem_val / divisor_val;
            let r_digit = rem_val % divisor_val;
            
            quotient.push(if q_digit == 1 { '1' } else { '0' });
            
            remainder.clear();
            if r_digit > 0 {
                let mut r_bits = Vec::new();
                let mut temp = r_digit;
                proof {
                    lemma_str2int_zero();
                }
                while temp > 0 {
                    invariant
                        ValidBitString(r_bits@),
                        Str2Int(r_bits@) == temp,
                    decreases temp
                    {
                    r_bits.push(if temp % 2 == 1 { '1' } else { '0' });
                    temp = temp / 2;
                }
                for r_bit in r_bits.iter().rev() {
                    remainder.push(*r_bit);
                }
            } else {
                remainder.push('0');
            }
        } else {
            quotient.push('0');
        }
        
        i += 1;
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

