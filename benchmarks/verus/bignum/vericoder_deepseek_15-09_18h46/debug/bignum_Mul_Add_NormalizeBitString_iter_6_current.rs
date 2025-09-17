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
proof fn lemma_sequence_last_spec<T>(v: Vec<T>) -> (last: Option<T>)
    ensures
        if v.len() > 0 { last == Some(v[v.len() - 1]) } else { last == None::<T> }
{
    if v.len() == 0 {
        None
    } else {
        Some(v[v.len() - 1])
    }
}

proof fn lemma_vec_pop_decreases_length<T>(v: &mut Vec<T>) 
    ensures v.len() == old(v).len() - 1
{
    v.pop();
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): Add decreases clause to while loop */
{
    let mut result = Vec::with_capacity(s1.len() + s2.len());
    
    for _ in 0..(s1.len() + s2.len()) {
        result.push('0');
    }
    
    let mut carry = 0;
    
    for i in 0..s1.len() {
        let mut temp_carry = 0;
        for j in 0..s2.len() {
            let bit1 = if s1[i] == '1' { 1 } else { 0 };
            let bit2 = if s2[j] == '1' { 1 } else { 0 };
            let product = bit1 * bit2 + temp_carry;
            let current_bit = if result[i + j] == '1' { 1 } else { 0 };
            let sum = current_bit + product + carry;
            
            result[i + j] = if (sum & 1) == 1 { '1' } else { '0' };
            carry = if sum >= 2 { 1 } else { 0 };
            temp_carry = if product >= 2 { 1 } else { 0 };
        }
        if carry > 0 {
            result[i + s2.len()] = if (carry & 1) == 1 { '1' } else { '0' };
            carry = if carry >= 2 { 1 } else { 0 };
        }
    }
    
    while result.len() > 0 && result[result.len() - 1] == '0'
        decreases result.len()
    {
        result.pop();
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
