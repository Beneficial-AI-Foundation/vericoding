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
/* helper modified by LLM (iteration 6): Fix helper_add_lemma parameter type to nat and ensure proper conversion */
proof fn helper_add_lemma(s1: Seq<char>, s2: Seq<char>, i: nat)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        i <= s1.len() && i <= s2.len()
    ensures
        Str2Int(s1.subrange(0, i as int).add(s2.subrange(0, i as int))) == Str2Int(s1.subrange(0, i as int)) + Str2Int(s2.subrange(0, i as int))
    decreases i
{
    if i > 0 {
        helper_add_lemma(s1, s2, i - 1);
    }
}

spec fn max(a: usize, b: usize) -> usize {
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
/* code modified by LLM (iteration 6): Convert max_len to nat for lemma call */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = max(len1, len2);
    
    let mut carry = false;
    let mut result = Vec::<char>::with_capacity(max_len + 1);
    
    let mut i: usize = 0;
    while i < max_len
        invariant
            0 <= i && i <= max_len,
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int)) + (if carry { 1nat } else { 0nat }),
            i >= len1 ==> s1@.subrange(0, i as int).len() == len1,
            i >= len2 ==> s2@.subrange(0, i as int).len() == len2
        decreases max_len - i
    {
        let bit1 = if i < len1 { s1[i] == '1' } else { false };
        let bit2 = if i < len2 { s2[i] == '1' } else { false };
        
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
    
    let max_len_nat = max_len as nat;
    helper_add_lemma(s1@, s2@, max_len_nat);
    
    result
}
// </vc-code>

fn main() {}
}