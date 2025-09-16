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
{
    /* code modified by LLM (iteration 2): fixed compilation error by using usize for loop index */
    let mut borrow: usize = 0;
    let len1: usize = s1.len();
    let len2: usize = s2.len();
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    let max_len: usize = if len1 > len2 { len1 } else { len2 };
    while i < max_len {
        let mut b1: usize = 0;
        if i < len1 {
            b1 = if s1[len1 - 1 - i] == '1' { 1 } else { 0 };
        }
        let mut b2: usize = 0;
        if i < len2 {
            b2 = if s2[len2 - 1 - i] == '1' { 1 } else { 0 };
        }
        let diff: isize = b1 as isize - b2 as isize - borrow as isize;
        let bit: usize;
        if diff >= 0 {
            bit = diff as usize;
            borrow = 0;
        } else {
            bit = (diff + 2) as usize;
            borrow = 1;
        }
        res.push(if bit == 1 { '1' } else { '0' });
        i += 1;
    }
    let mut rres: Vec<char> = Vec::new();
    let mut idx: usize = res.len();
    while idx > 0 {
        idx -= 1;
        rres.push(res[idx]);
    }
    let mut start: usize = 0;
    while start < rres.len() && rres[start] == '0' {
        start += 1;
    }
    if start == rres.len() {
        start = rres.len() - 1;
    }
    let mut final_res: Vec<char> = Vec::new();
    let mut j: usize = start;
    while j < rres.len() {
        final_res.push(rres[j]);
        j += 1;
    }
    final_res
}
// </vc-code>

fn main() {}
}


