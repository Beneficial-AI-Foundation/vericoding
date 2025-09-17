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

// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>

    /* code modified by LLM (iteration 3): fixed reverse iteration by using forward loop with index calculation */
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    let mut vec1: Vec<char> = Vec::with_capacity(max_len);
    for _ in 0..(max_len - s1.len()) {
        vec1.push('0');
    }
    for &c in s1 {
        vec1.push(c);
    }
    let mut vec2: Vec<char> = Vec::with_capacity(max_len);
    for _ in 0..(max_len - s2.len()) {
        vec2.push('0');
    }
    for &c in s2 {
        vec2.push(c);
    }
    let mut res_vec: Vec<char> = Vec::new();
    let mut borrow = 0i32;
    for i in 0..max_len {
        let idx = (max_len - 1 - i) as usize;
        let b1 = vec1[idx] as i32 - ('0' as i32);
        let b2 = vec2[idx] as i32 - ('0' as i32);
        let mut current = b1 - b2 - borrow;
        if current < 0 {
            current += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        let char_digit = ('0' as u8 + current as u8) as char;
        res_vec.push(char_digit);
    }
    res_vec.reverse();
    res_vec

// </vc-code>

fn main() {}
}


