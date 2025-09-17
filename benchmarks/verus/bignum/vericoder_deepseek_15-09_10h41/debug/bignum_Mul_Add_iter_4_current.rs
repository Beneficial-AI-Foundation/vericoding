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
/* helper modified by LLM (iteration 4): Remove std library reverse dependency */
fn reverse_string(s: &Vec<char>) -> (result: Vec<char>)
    ensures result@ == s@.reverse(), ValidBitString(result@)
{
    let mut res: Vec<char> = Vec::new();
    let len = s.len();
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            res@ == s@.subrange(len - i as int, len as int).reverse(),
            ValidBitString(res@)
    {
        res.push(s[len - 1 - i]);
        i += 1;
    }
    res
}

/* helper modified by LLM (iteration 4): Manual max function */
fn max(a: usize, b: usize) -> (result: usize)
    ensures a >= b ==> result == a,
            a < b ==> result == b
{
    if a >= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Remove std reverse() call and use custom reverse helper */
{
    let mut result: Vec<char> = Vec::new();
    let s2_len = s2.len();
    
    let mut carry = 0;
    for i in 0..s2_len {
        let bit2 = s2[s2_len - 1 - i];
        let mut partial: Vec<char> = Vec::new();
        
        // Add i zeros (shift left)
        for _ in 0..i {
            partial.push('0');
        }
        
        // Multiply s1 by the current bit in s2
        for j in 0..s1.len() {
            let bit1 = s1[s1.len() - 1 - j];
            let product = if bit1 == '1' && bit2 == '1' { 1 } else { 0 };
            let sum = product + carry;
            carry = if sum >= 2 { 1 } else { 0 };
            partial.push(if sum % 2 == 1 { '1' } else { '0' });
        }
        
        if carry > 0 {
            partial.push('1');
            carry = 0;
        }
        
        // Add this partial result to the total
        let mut new_result = Vec::new();
        let max_len = max(result.len(), partial.len());
        for k in 0..max_len {
            let a = if k < result.len() && result[k] == '1' { 1 } else { 0 };
            let b = if k < partial.len() && partial[k] == '1' { 1 } else { 0 };
            let sum = a + b + carry;
            carry = if sum >= 2 { 1 } else { 0 };
            new_result.push(if sum % 2 == 1 { '1' } else { '0' });
        }
        
        if carry > 0 {
            new_result.push('1');
            carry = 0;
        }
        
        result = new_result;
    }
    
    reverse_string(&result)
}
// </vc-code>

fn main() {}
}
