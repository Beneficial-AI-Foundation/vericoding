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

// <vc-helpers>

proof fn helper_add_lemma(s1: Seq<char>, s2: Seq<char>, i: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= i && i <= s1.len() as int && i <= s2.len() as int
    ensures
        Str2Int(s1.subrange(0, i).add(s2.subrange(0, i))) == Str2Int(s1.subrange(0, i)) + Str2Int(s2.subrange(0, i))
    decreases i
{
    if i > 0 {
        helper_add_lemma(s1, s2, i - 1);
    }
}

spec fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
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
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = max(len1 as int, len2 as int) as usize;
    
    let mut carry = false;
    let mut result = Vec::<char>::with_capacity(max_len + 1);
    
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i && i <= max_len as int,
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@.subrange(0, i)) + Str2Int(s2@.subrange(0, i)) + (if carry { 1nat } else { 0nat }),
            i >= len1 as int ==> s1@.subrange(0, i).len() == len1,
            i >= len2 as int ==> s2@.subrange(0, i).len() == len2
        decreases max_len as int - i
    {
        let bit1 = if i < len1 as int && i < len1 as int { s1[i as usize] == '1' } else { false };
        let bit2 = if i < len2 as int && i < len2 as int { s2[i as usize] == '1' } else { false };
        
        let sum = if bit1 { 1 } else { 0 } + if bit2 { 1 } else { 0 } + if carry { 1 } else { 0 };
        
        match sum {
            0 => {
                result.push('0');
                carry = false;
            },
            1 => {
                result.push('1');
                carry = false;
            },
            2 => {
                result.push('0');
                carry = true;
            },
            _ => {
                result.push('1');
                carry = true;
            }
        }
        
        i = i + 1;
    }
    
    if carry {
        result.push('1');
    }
    
    helper_add_lemma(s1@, s2@, max_len as int);
    
    result
}
// </vc-code>

fn main() {}
}