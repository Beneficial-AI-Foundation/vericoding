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
/* helper modified by LLM (iteration 10): Remove problematic int/nat conversions and use proper ghost types */
spec fn char_to_digit_ghost(c: char) -> nat
{
    if c == '1' { 1nat } else { 0nat }
}

spec fn digit_to_char_ghost(d: nat) -> char
{
    if d == 1 { '1' } else { '0' }
}

fn char_to_digit_comp(c: char) -> u8
{
    if c == '1' { 1 } else { 0 }
}

fn digit_to_char_comp(d: u8) -> char
{
    if d == 1 { '1' } else { '0' }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fix int/nat conversion errors and ensure proper type usage */
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
        let idx1 = (len1 as isize - 1 - i as isize) as usize;
        let idx2 = (len2 as isize - 1 - i as isize) as usize;
        
        let d1 = if i < len1 { char_to_digit_comp(s1[idx1]) } else { 0 };
        let d2 = if i < len2 { char_to_digit_comp(s2[idx2]) } else { 0 };
        
        let mut diff = d1 as i32 - d2 as i32 - borrow;
        if diff < 0 {
            diff += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        
        res.push(digit_to_char_comp(diff as u8));
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


