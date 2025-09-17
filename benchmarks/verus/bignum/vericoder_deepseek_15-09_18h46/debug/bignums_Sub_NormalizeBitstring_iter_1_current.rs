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

proof fn lemma_str2int_positive(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_positive(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1) && ValidBitString(s2) && s1.len() <= s2.len()
    ensures Str2Int(s1) <= Str2Int(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(Str2Int(s1) == 0);
    } else if s2.len() == 0 {
    } else {
        lemma_str2int_monotonic(s1.subrange(0, s1.len() as int - 1), s2.subrange(0, s2.len() as int - 1));
    }
}

fn is_zero(s: &[char]) -> (res: bool)
    requires ValidBitString(s@)
    ensures res == (Str2Int(s@) == 0)
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i,
            i <= s.len(),
            forall |j| 0 <= j && j < i ==> s@[j] == '0'
    {
        if s[i] != '0' {
            return false;
        }
        i += 1;
    }
    true
}

// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut leading_zeros_skipped = false;
    
    for i in 0..s.len() {
        if !leading_zeros_skipped && s[i] == '0' {
            continue;
        }
        leading_zeros_skipped = true;
        result.push(s[i]);
    }
    
    if result.is_empty() {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
