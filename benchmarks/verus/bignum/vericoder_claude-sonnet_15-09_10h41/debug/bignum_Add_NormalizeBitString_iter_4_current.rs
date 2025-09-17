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
{
    /* code modified by LLM (iteration 4): removed result.reverse() call to fix compilation error */
    let mut result = Vec::<char>::new();
    
    if s.len() == 0 {
        result.push('0');
        return result;
    }
    
    let mut start_idx = 0;
    while start_idx < s.len() && s[start_idx] == '0'
        invariant
            start_idx <= s.len(),
            ValidBitString(s@),
    {
        start_idx += 1;
    }
    
    if start_idx == s.len() {
        result.push('0');
        return result;
    }
    
    let mut i = start_idx;
    while i < s.len()
        invariant
            start_idx <= i <= s.len(),
            ValidBitString(s@),
            ValidBitString(result@),
            start_idx < s.len() ==> s[start_idx as int] == '1',
    {
        result.push(s[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added manual reverse implementation */
exec fn reverse_vec(v: &mut Vec<char>)
    ensures
        v@.len() == old(v)@.len(),
        forall |i: int| 0 <= i < v@.len() ==> v@[i] == old(v)@[v@.len() - 1 - i],
{
    let len = v.len();
    let mut i = 0;
    while i < len / 2
        invariant
            i <= len / 2,
            v@.len() == len,
            forall |j: int| 0 <= j < i ==> v@[j] == old(v)@[len - 1 - j],
            forall |j: int| 0 <= j < i ==> v@[len - 1 - j] == old(v)@[j],
            forall |j: int| i <= j < len - i ==> v@[j] == old(v)@[j],
    {
        let temp = v[i];
        v.set(i, v[len - 1 - i]);
        v.set(len - 1 - i, temp);
        i += 1;
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
{
    /* code modified by LLM (iteration 4): replaced result.reverse() with manual reverse */
    let mut result = Vec::<char>::new();
    let mut carry: usize = 0;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            i1 <= s1.len(),
            i2 <= s2.len(),
            carry <= 1,
            ValidBitString(s1@),
            ValidBitString(s2@),
            ValidBitString(result@),
    {
        let mut sum = carry;
        
        if i1 > 0 {
            i1 -= 1;
            if s1[i1] == '1' {
                sum += 1;
            }
        }
        
        if i2 > 0 {
            i2 -= 1;
            if s2[i2] == '1' {
                sum += 1;
            }
        }
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        carry = sum / 2;
    }
    
    reverse_vec(&mut result);
    result
}
// </vc-code>

fn main() {}
}


