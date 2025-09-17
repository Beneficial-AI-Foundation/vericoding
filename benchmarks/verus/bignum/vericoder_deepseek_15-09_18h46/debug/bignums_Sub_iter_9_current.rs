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
/* helper modified by LLM (iteration 9): Add helper functions for binary arithmetic operations */
fn char_to_digit(c: char) -> u8 {
    if c == '1' { 1 } else { 0 }
}

fn digit_to_char(d: u8) -> char {
    if d == 1 { '1' } else { '0' }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Implement binary subtraction algorithm without reverse() method */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    
    let mut res = Vec::<char>::new();
    let mut borrow = 0;
    
    let mut i = 0;
    while i < max_len
        invariant
            i <= max_len,
    {
        let idx1 = len1 as int - 1 - i;
        let idx2 = len2 as int - 1 - i;
        
        let d1 = if idx1 >= 0 { char_to_digit(s1[idx1 as usize]) } else { 0 };
        let d2 = if idx2 >= 0 { char_to_digit(s2[idx2 as usize]) } else { 0 };
        
        let mut diff = d1 as i32 - d2 as i32 - borrow;
        if diff < 0 {
            diff += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        
        res.push(digit_to_char(diff as u8));
        i += 1;
    }
    
    // Remove leading zeros
    while res.len() > 1 && res[res.len() - 1] == '0' {
        res.pop();
    }
    
    // Build result in correct order
    let mut result_vec = Vec::<char>::new();
    let mut j = res.len();
    while j > 0
        invariant
            j <= res.len(),
    {
        j -= 1;
        result_vec.push(res[j]);
    }
    
    if result_vec.is_empty() {
        result_vec.push('0');
    }
    
    result_vec
}
// </vc-code>

fn main() {}
}


