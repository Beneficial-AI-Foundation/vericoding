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
/* helper modified by LLM (iteration 8): Fix compilation errors and remove problematic helpers */
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

spec fn nat_to_int(n: nat) -> int
{
    n as int
}

proof fn lemma_nat_to_int_positive(n: nat)
    ensures nat_to_int(n) >= 0,
{
}

spec fn int_to_nat(i: int) -> nat
    requires i >= 0,
{
    i as nat  
}

spec fn is_char_zero(c: char) -> bool {
    c == '0'
}

spec fn is_char_one(c: char) -> bool {
    c == '1'
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
/* code modified by LLM (iteration 8): Fix type conversion errors and simplify implementation */
{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    let divisor_val = Str2Int(divisor@);
    
    proof {
        lemma_divmod_recursive(Seq::<char>::empty(), divisor@);
    }
    
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            i >= 0,
            i <= dividend.len(),
            ValidBitString(quotient@) && ValidBitString(remainder@),
            Str2Int(remainder@) < divisor_val,
            Str2Int(quotient@) * divisor_val + Str2Int(remainder@) == Str2Int(dividend@.subrange(0, i as int)),
        decreases dividend.len() - i
    {
        let bit = dividend[i];
        remainder.push(bit);
        
        if Str2Int(remainder@) >= divisor_val {
            let rem_val = Str2Int(remainder@);
            proof {
                lemma_divmod_step(remainder@.subrange(0, remainder.len() as int - 1), divisor@, bit);
            }
            let q_digit: nat = rem_val / divisor_val;
            let r_digit: nat = rem_val % divisor_val;
            
            quotient.push(if q_digit == 1nat { '1' } else { '0' });
            
            remainder.clear();
            if r_digit > 0nat {
                let mut temp: nat = r_digit;
                let mut r_bits = Vec::new();
                while temp > 0nat
                    invariant
                        ValidBitString(r_bits@),
                        Str2Int(r_bits@) == temp,
                    decreases temp
                {
                    r_bits.push(if temp % 2nat == 1nat { '1' } else { '0' });
                    temp = temp / 2nat;
                }
                let mut idx: isize = (r_bits.len() as isize) - 1;
                while idx >= 0
                    invariant
                        0 <= idx && idx < r_bits.len() as isize || (idx < 0 && idx >= -1),
                        ValidBitString(remainder@),
                    decreases idx
                {
                    remainder.push(r_bits[r_bits.len() - 1 - idx as usize]);
                    idx -= 1;
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

