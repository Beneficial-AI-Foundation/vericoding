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
    /* code modified by LLM (iteration 2): Fixed integer conversions to avoid ghost/nat type errors in exec code */
    let mut t = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i >= 0,
            i <= s.len(),
            ValidBitString(t@),
            s@.subrange(0, i as int).len() == t@.len(),
            Str2Int(s@.subrange(0, i as int)) == Str2Int(t@)
        decreases s.len() - i
    {
        if s[i] == '1' {
            t.push('1');
        } else if !t.is_empty() {
            t.push('0');
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
/* helper modified by LLM (iteration 2): Fixed find_first_one to use usize parameters and return int */
fn find_first_one(s: Seq<char>, start: int) -> (index: int)
    requires start >= 0, start <= s.len() as int
    ensures index >= start, index <= s.len() as int, forall |i: int| start <= i && i < index ==> s.index(i) == '0', index < s.len() as int ==> s.index(index) == '1'
{
    if start >= s.len() as int {
        s.len() as int
    } else if s.index(start) == '1' {
        start
    } else {
        find_first_one(s, start + 1)
    }
}

proof fn str2int_zero_prefix_lemma(s: Seq<char>, n: int)
    requires ValidBitString(s), n >= 0, n <= s.len() as int
    ensures Str2Int(s.subrange(0, n)) == Str2Int(s.subrange(find_first_one(s, 0), n))
    decreases n - find_first_one(s, 0)
{
    if n > find_first_one(s, 0) {
        str2int_zero_prefix_lemma(s, n - 1);
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
    /* code modified by LLM (iteration 2): Fixed integer conversions to avoid ghost/nat type errors in exec code */
    let mut carry = 0;
    let mut i: isize = s1.len() as isize - 1;
    let mut j: isize = s2.len() as isize - 1;
    let mut res = Vec::new();
    
    while i >= 0 || j >= 0 || carry > 0
        invariant
            i >= -1, j >= -1, carry >= 0, carry <= 1,
            ValidBitString(res@),
            Str2Int(res@) + (carry as nat) * (2 as nat).pow((res.len() as nat)) == 
                Str2Int(s1@.subrange(i + 1, s1.len() as int)) + Str2Int(s2@.subrange(j + 1, s2.len() as int))
        decreases i + j + carry
    {
        let mut sum = carry;
        
        if i >= 0 {
            sum = sum + (if s1[i as usize] == '1' { 1 } else { 0 });
            i = i - 1;
        }
        
        if j >= 0 {
            sum = sum + (if s2[j as usize] == '1' { 1 } else { 0 });
            j = j - 1;
        }
        
        if sum % 2 == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        
        carry = sum / 2;
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


