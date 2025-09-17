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
proof fn lemma_str2int_subrange_prefix(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i,
        i <= s.len() as int,
    ensures
        ValidBitString(s.subrange(i, s.len() as int)),
{
}

proof fn lemma_str2int_empty_subrange(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
    ensures
        s.subrange(1, s.len() as int).len() == s.len() - 1,
{
}

proof fn lemma_str2int_preservation(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        s[0] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(1, s.len() as int)),
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: single '0'
    } else {
        let tail = s.subrange(1, s.len() as int);
        lemma_str2int_subrange_prefix(s, 1);
        lemma_str2int_empty_subrange(s);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut start_idx = 0;
    
    // Find first non-zero character
    while start_idx < s.len()
        invariant
            start_idx <= s.len(),
            forall |i: int| 0 <= i && i < start_idx ==> s@[i] == '0',
    {
        if s[start_idx] != '0' {
            break;
        }
        start_idx += 1;
    }
    
    // If all zeros, return "0"
    if start_idx == s.len() {
        result.push('0');
        return result;
    }
    
    // Copy from first non-zero to end
    let mut i = start_idx;
    while i < s.len()
        invariant
            start_idx <= i,
            i <= s.len(),
            result@.len() == i - start_idx,
            forall |j: int| 0 <= j && j < result@.len() ==> result@[j] == s@[start_idx + j],
            start_idx < s.len(),
            s@[start_idx] != '0',
    {
        result.push(s[i]);
        i += 1;
    }
    
    proof {
        if ValidBitString(s@) {
            lemma_str2int_preservation(s@);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


