
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
/* helper modified by LLM (iteration 5): fixed nat literal syntax using int with explicit casts and added proper Verus power function */
use vstd::arithmetic::power2::pow2;

proof fn lemma_div_mod_properties(dividend: nat, divisor: nat) 
    requires
        divisor > 0,
    ensures
        dividend / divisor <= dividend,
        dividend % divisor < divisor,
        dividend == divisor * (dividend / divisor) + dividend % divisor
{
}

spec fn subrange(s: Seq<char>, start: int, end: int) -> Seq<char>
    recommends 0 <= start && start <= end && end <= s.len() as int
{
    s.subrange(start, end)
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed nat literals to use int/u32 with explicit casts and corrected power function usage */
{
    proof {
        lemma_div_mod_properties(Str2Int(dividend@), Str2Int(divisor@));
    }
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    let mut current: int = 0;
    let divisor_val = Str2Int(divisor@) as int;
    
    for i in 0..dividend.len()
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            current < divisor_val,
            (Str2Int(quotient@) as int) * divisor_val + current == Str2Int(subrange(dividend@, 0, i as int)) as int,
    {
        current = current * 2 + (if dividend[i] == '1' { 1 } else { 0 });
        
        if current >= divisor_val {
            quotient.push('1');
            current = current - divisor_val;
        } else {
            quotient.push('0');
        }
    }
    
    for _ in 0..divisor.len() - 1 {
        remainder.push('0');
    }
    
    let mut temp = current;
    let len_minus_one = divisor.len() - 1;
    for i in 0..len_minus_one
        invariant
            ValidBitString(remainder@),
            Str2Int(remainder@) as int == temp % (pow2((len_minus_one - i) as u32) as int),
    {
        let idx = len_minus_one - 1 - i;
        if temp % 2 == 1 {
            remainder[idx] = '1';
        } else {
            remainder[idx] = '0';
        }
        temp = temp / 2;
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


