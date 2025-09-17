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
/* helper modified by LLM (iteration 4): fixed type error by casting start_idx to int */
spec fn is_zero_string(s: Seq<char>) -> bool
{
    s.len() > 0 && (forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0')
}

proof fn lemma_zero_string_value(s: Seq<char>)
    requires ValidBitString(s), is_zero_string(s)
    ensures Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_zero_string_value(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_remove_leading_zeros(s: Seq<char>)
    requires ValidBitString(s), s.len() > 1, s[0] == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    let tail = s.subrange(1, s.len() as int);
    assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }));
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed type error by casting start_idx to int */
    let mut result = Vec::new();
    let mut start_idx = 0;
    
    if s.len() == 0 {
        result.push('0');
        return result;
    }
    
    while start_idx < s.len() && s[start_idx] == '0'
        invariant
            start_idx <= s.len(),
            ValidBitString(s@),
            forall |i: int| 0 <= i && i < start_idx ==> s@[i] == '0',
        decreases s.len() - start_idx
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
            start_idx <= i,
            i <= s.len(),
            ValidBitString(s@),
            ValidBitString(result@),
            result@.len() == i - start_idx,
            forall |j: int| 0 <= j && j < result@.len() ==> result@[j] == s@[start_idx + j],
            start_idx < s.len() ==> s@[start_idx as int] != '0',
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


