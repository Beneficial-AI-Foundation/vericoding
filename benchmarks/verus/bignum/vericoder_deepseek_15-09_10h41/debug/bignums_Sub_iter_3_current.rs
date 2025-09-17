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
proof fn lemma_Str2Int_monotonic(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i <= s.len() as int
    ensures Str2Int(s.subrange(0, i)) <= Str2Int(s)
    decreases s.len() - i as nat
{
    if i < s.len() as int {
        lemma_Str2Int_monotonic(s, i + 1);
    }
}

proof fn lemma_Str2Int_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
}

proof fn lemma_subrange_len(s: Seq<char>, start: int, end: int)
    requires 0 <= start <= end <= s.len() as int
    ensures s.subrange(start, end).len() == end - start
{
}

proof fn lemma_reverse_preserves_validity(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s.reverse())
{
}

proof fn lemma_reverse_preserves_Str2Int(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.reverse()) == Str2Int(s)
{
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Replaced reverse() with manual reversal to avoid unsupported function */
    let mut result = Vec::new();
    let mut i = s1.len() as isize - 1;
    let mut j = s2.len() as isize - 1;
    let mut borrow = 0;
    
    while i >= 0 || j >= 0 {
        let bit1 = if i >= 0 { if s1[i as usize] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if j >= 0 { if s2[j as usize] == '1' { 1 } else { 0 } } else { 0 };
        
        let mut diff = bit1 - bit2 - borrow;
        borrow = 0;
        
        if diff < 0 {
            diff += 2;
            borrow = 1;
        }
        
        result.push(if diff == 1 { '1' } else { '0' });
        
        i -= 1;
        j -= 1;
    }
    
    // Manual reversal instead of using reverse()
    let mut reversed_result = Vec::new();
    let mut idx = result.len() as isize - 1;
    while idx >= 0 {
        reversed_result.push(result[idx as usize]);
        idx -= 1;
    }
    
    while reversed_result.len() > 0 && reversed_result[0] == '0' {
        reversed_result.remove(0);
    }
    
    if reversed_result.len() == 0 {
        reversed_result.push('0');
    }
    
    reversed_result
}
// </vc-code>

fn main() {}
}


