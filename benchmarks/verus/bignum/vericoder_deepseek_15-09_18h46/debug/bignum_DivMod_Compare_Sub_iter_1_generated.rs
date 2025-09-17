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
    ensures dividend / divisor == (dividend - (dividend % divisor)) / divisor,
        dividend % divisor == dividend - (dividend / divisor) * divisor
{
}

proof fn lemma_div_mod_identity(dividend: nat, divisor: nat)
    requires divisor > 0
    ensures dividend == (dividend / divisor) * divisor + dividend % divisor
{
}

proof fn lemma_str2int_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), s1.len() <= s2.len()
    ensures Str2Int(s1) <= Str2Int(s2)
{
}

fn compare_strings(a: &[char], b: &[char]) -> bool
    requires ValidBitString(a@), ValidBitString(b@)
    ensures result == (Str2Int(a@) >= Str2Int(b@))
{
    if a.len() < b.len() {
        false
    } else if a.len() > b.len() {
        true
    } else {
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                forall |j: int| 0 <= j < i ==> a[j] == b[j],
                Str2Int(a.subrange(0, i as int)) == Str2Int(b.subrange(0, i as int))
            decreases a.len() - i
        {
            if a[i] == '1' && b[i] == '0' {
                return true;
            } else if a[i] == '0' && b[i] == '1' {
                return false;
            }
            i += 1;
        }
        true
    }
}

fn subtract_strings(a: &[char], b: &[char]) -> Vec<char>
    requires ValidBitString(a@), ValidBitString(b@), Str2Int(a@) >= Str2Int(b@)
    ensures ValidBitString(result@), Str2Int(result@) == Str2Int(a@) - Str2Int(b@)
{
    let mut result = Vec::new();
    let mut borrow = false;
    let mut i = (a.len() as int - 1) as usize;
    
    while i >= 0 && i < a.len()
        invariant
            i >= 0 && i <= a.len(),
            ValidBitString(result@),
            Str2Int(result@) + (if borrow { 1 } else { 0 }) * pow2(a.len() - i - 1) == 
                Str2Int(a.subrange(i as int, a.len() as int)) - Str2Int(b.subrange(i as int, b.len() as int))
        decreases i
    {
        let a_bit = a[i] == '1';
        let b_bit = if i < b.len() { b[i] == '1' } else { false };
        
        let mut diff = (a_bit as u8) - (b_bit as u8) - (borrow as u8);
        borrow = diff < 0;
        if borrow {
            diff += 2;
        }
        
        result.push(if diff == 1 { '1' } else { '0' });
        i -= 1;
    }
    
    result.reverse();
    result
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
{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    proof {
        lemma_str2int_nonnegative(divisor@);
    }
    
    if !compare_strings(dividend, divisor) {
        quotient.push('0');
        remainder.extend_from_slice(dividend);
        return (quotient, remainder);
    }
    
    let mut current = Vec::new();
    let mut i = 0;
    
    while i < dividend.len()
        invariant
            0 <= i <= dividend.len(),
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            ValidBitString(current@),
            Str2Int(dividend@) == Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(remainder@),
            Str2Int(remainder@) < Str2Int(divisor@),
            Str2Int(current@) == Str2Int(dividend.subrange(0, i as int))
        decreases dividend.len() - i
    {
        current.push(dividend[i]);
        
        if compare_strings(&current, divisor) {
            quotient.push('1');
            let subtracted = subtract_strings(&current, divisor);
            current = subtracted;
        } else {
            quotient.push('0');
        }
        
        i += 1;
    }
    
    remainder = current;
    
    proof {
        lemma_div_mod_identity(Str2Int(dividend@), Str2Int(divisor@));
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

