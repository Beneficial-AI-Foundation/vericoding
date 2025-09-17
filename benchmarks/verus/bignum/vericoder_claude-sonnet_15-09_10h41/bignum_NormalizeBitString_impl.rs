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
/* helper modified by LLM (iteration 5): fixed lemma preconditions and proof structure */
spec fn is_zero_string(s: Seq<char>) -> bool
{
    s.len() > 0 && (forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0')
}

proof fn lemma_zero_string_value(s: Seq<char>)
    requires ValidBitString(s), is_zero_string(s), s.len() > 0
    ensures Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == '0');
    } else {
        let sub = s.subrange(0, s.len() as int - 1);
        assert(is_zero_string(sub));
        lemma_zero_string_value(sub);
        assert(s[s.len() as int - 1] == '0');
    }
}

proof fn lemma_remove_leading_zeros(s: Seq<char>)
    requires ValidBitString(s), s.len() > 1, s[0] == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 2 {
        let tail = s.subrange(1, 2);
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, 1)) + (if s[1] == '1' { 1nat } else { 0nat }));
        assert(s.subrange(0, 1)[0] == '0');
        assert(Str2Int(s.subrange(0, 1)) == 0);
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        let tail = s.subrange(1, s.len() as int);
        let tail_prefix = tail.subrange(0, tail.len() as int - 1);
        assert(prefix.subrange(1, prefix.len() as int) =~= tail_prefix);
        lemma_remove_leading_zeros(prefix);
        assert(Str2Int(prefix) == Str2Int(tail_prefix));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proof calls and fixed invariants */
    let mut result = Vec::new();
    let mut start_idx = 0;
    
    if s.len() == 0 {
        result.push('0');
        return result;
    }
    
    proof {
        assert(ValidBitString(s@));
    }
    
    while start_idx < s.len() && s[start_idx] == '0'
        invariant
            start_idx <= s.len(),
            forall |i: int| 0 <= i && i < start_idx ==> s@[i] == '0',
        decreases s.len() - start_idx
    {
        start_idx += 1;
    }
    
    if start_idx == s.len() {
        result.push('0');
        proof {
            assert(is_zero_string(s@));
            lemma_zero_string_value(s@);
        }
        return result;
    }
    
    let mut i = start_idx;
    while i < s.len()
        invariant
            start_idx <= i,
            i <= s.len(),
            ValidBitString(result@),
            result@.len() == i - start_idx,
            forall |j: int| 0 <= j && j < result@.len() ==> result@[j] == s@[start_idx + j],
            start_idx < s.len() ==> s@[start_idx as int] != '0',
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    
    proof {
        if start_idx > 0 {
            let mut k = 0;
            while k < start_idx
                invariant 0 <= k <= start_idx
            {
                if k == 0 {
                    lemma_remove_leading_zeros(s@.subrange(k, s.len() as int));
                }
                k += 1;
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


