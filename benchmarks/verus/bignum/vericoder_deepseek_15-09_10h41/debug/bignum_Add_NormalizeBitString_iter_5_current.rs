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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors by using proper int indexing and vector operations */
{
    let mut t = Vec::new();
    let mut i: int = 0;
    let mut found_one = false;
    
    while i < s.len() as int
        invariant
            i <= s.len() as int,
            forall |j: int| 0 <= j && j < t.len() as int ==> (t@[j] == '0' || t@[j] == '1'),
            found_one ==> t.len() > 0 && t@[0] == '1',
            !found_one ==> t.is_empty()
        decreases s.len() as int - i
    {
        if s[i as usize] == '1' && !found_one {
            t.push('1');
            found_one = true;
        } else if found_one {
            t.push(s[i as usize]);
        }
        i = i + 1;
    }
    
    if t.is_empty() {
        t.push('0');
    }
    
    t
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type annotations and proper int indexing */
spec fn find_first_one(s: Seq<char>, start: int) -> (index: int)
    requires start >= 0, start <= s.len() as int
    ensures index >= start, index <= s.len() as int, 
        forall |i: int| start <= i && i < index ==> s[i] == '0', 
        index < s.len() as int ==> s[index] == '1'
{
    if start >= s.len() as int {
        s.len() as int
    } else if s[start] == '1' {
        start
    } else {
        find_first_one(s, start + 1)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed integer conversions and proper vector indexing with int types */
{
    let mut carry: int = 0;
    let max_len = if s1.len() > s2.len() { s1.len() as int } else { s2.len() as int };
    let mut res = Vec::new();
    
    for idx in 0..max_len {
        let mut sum = carry;
        
        if idx < s1.len() as int {
            sum += if s1@[(s1.len() as int - 1 - idx)] == '1' { 1 } else { 0 };
        }
        
        if idx < s2.len() as int {
            sum += if s2@[(s2.len() as int - 1 - idx)] == '1' { 1 } else { 0 };
        }
        
        if sum % 2 == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        
        carry = sum / 2;
    }
    
    if carry > 0 {
        res.push('1');
    }
    
    res.reverse();
    
    if res.is_empty() {
        res.push('0');
    }
    
    res
}
// </vc-code>

fn main() {}
}


