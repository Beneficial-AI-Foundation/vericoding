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

// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut s1_chars = s1.iter();
    let mut s2_chars = s2.iter();
    let mut borrow = 0;
    
    while let (Some(&c1), Some(&c2)) = (s1_chars.next_back(), s2_chars.next_back()) {
        let bit1 = if c1 == '1' { 1 } else { 0 };
        let bit2 = if c2 == '1' { 1 } else { 0 };
        
        let mut diff = bit1 - bit2 - borrow;
        borrow = 0;
        
        if diff < 0 {
            diff += 2;
            borrow = 1;
        }
        
        result.push(if diff == 1 { '1' } else { '0' });
    }
    
    while let Some(&c1) = s1_chars.next_back() {
        let bit1 = if c1 == '1' { 1 } else { 0 };
        let mut diff = bit1 - borrow;
        borrow = 0;
        
        if diff < 0 {
            diff += 2;
            borrow = 1;
        }
        
        result.push(if diff == 1 { '1' } else { '0' });
    }
    
    result.reverse();
    
    while result.len() > 0 && result[0] == '0' {
        result.remove(0);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}


