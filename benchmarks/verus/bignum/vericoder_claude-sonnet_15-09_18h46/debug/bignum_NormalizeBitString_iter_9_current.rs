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

/* helper modified by LLM (iteration 9): simplified proof to establish equality for removing leading zeros */
proof fn lemma_str2int_preservation(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        s[0] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(1, s.len() as int)),
    decreases s.len()
{
    let tail = s.subrange(1, s.len() as int);
    lemma_str2int_subrange_prefix(s, 1);
    
    if s.len() == 1 {
        assert(tail.len() == 0);
        assert(Str2Int(tail) == 0);
        assert(Str2Int(s) == 0);
    } else {
        assert(s.index(s.len() as int - 1) == tail.index(tail.len() as int - 1));
        assert(s.subrange(0, s.len() as int - 1) == tail.subrange(0, tail.len() as int - 1));
        assert(Str2Int(s) == 2 * Str2Int(tail.subrange(0, tail.len() as int - 1)) + (if tail.index(tail.len() as int - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s) == Str2Int(tail));
    }
}

/* helper modified by LLM (iteration 9): lemma for removing multiple leading zeros */
proof fn lemma_str2int_remove_leading_zeros(s: Seq<char>, start: int)
    requires
        ValidBitString(s),
        0 <= start,
        start <= s.len() as int,
        forall |i: int| 0 <= i && i < start ==> s[i] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(start, s.len() as int)),
    decreases start
{
    if start == 0 {
        assert(s.subrange(0, s.len() as int) == s);
    } else {
        lemma_str2int_preservation(s);
        lemma_str2int_remove_leading_zeros(s.subrange(1, s.len() as int), start - 1);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): simplified proof and fixed assertions */
    let mut result = Vec::new();
    let mut start_idx: usize = 0;
    
    // Find first non-zero character
    while start_idx < s.len()
        invariant
            start_idx <= s.len(),
            forall |i: int| 0 <= i && i < start_idx as int ==> s@[i] == '0',
        decreases s.len() - start_idx
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
            forall |j: int| 0 <= j && j < result@.len() ==> result@[j] == s@[start_idx as int + j],
            start_idx < s.len(),
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    
    proof {
        if ValidBitString(s@) {
            lemma_str2int_remove_leading_zeros(s@, start_idx as int);
            assert(s@.subrange(start_idx as int, s@.len() as int) == result@);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


