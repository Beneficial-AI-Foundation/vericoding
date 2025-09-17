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
proof fn lemma_str2int_zero_prefix(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        s[0] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(1, s.len() as int)),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.subrange(1, s.len() as int).len() == 0);
        assert(Str2Int(s) == 0);
        assert(Str2Int(s.subrange(1, s.len() as int)) == 0);
    } else {
        let s_rest = s.subrange(0, s.len() as int - 1);
        let s_tail = s.subrange(1, s.len() as int);
        let s_tail_rest = s_tail.subrange(0, s_tail.len() as int - 1);
        
        assert(s_rest.len() > 0);
        assert(s_rest[0] == '0');
        assert(ValidBitString(s_rest)) by {
            assert forall |i: int| 0 <= i && i < s_rest.len() as int implies
                (s_rest[i] == '0' || s_rest[i] == '1') by {
                assert(s_rest[i] == s[i]);
            }
        }
        
        assert(s_tail_rest =~= s_rest.subrange(1, s_rest.len() as int)) by {
            assert(s_tail.len() == s.len() - 1);
            assert(s_tail_rest.len() == s_tail.len() - 1);
            assert forall |i: int| 0 <= i && i < s_tail_rest.len() as int implies
                s_tail_rest[i] == s_rest.subrange(1, s_rest.len() as int)[i] by {
                assert(s_tail_rest[i] == s_tail[i]);
                assert(s_tail[i] == s[i + 1]);
                assert(s_rest.subrange(1, s_rest.len() as int)[i] == s_rest[i + 1]);
                assert(s_rest[i + 1] == s[i + 1]);
            }
        }
        
        lemma_str2int_zero_prefix(s_rest);
        assert(Str2Int(s_rest) == Str2Int(s_rest.subrange(1, s_rest.len() as int)));
        
        let last_char = s[s.len() as int - 1];
        let last_val = if last_char == '1' { 1nat } else { 0nat };
        
        assert(Str2Int(s) == 2 * Str2Int(s_rest) + last_val);
        assert(Str2Int(s_tail) == 2 * Str2Int(s_tail_rest) + last_val);
        assert(s_tail[s_tail.len() as int - 1] == last_char);
    }
}

proof fn lemma_valid_subrange(s: Seq<char>, start: int, end: int)
    requires
        ValidBitString(s),
        0 <= start <= end <= s.len() as int,
    ensures
        ValidBitString(s.subrange(start, end)),
{
    let sub = s.subrange(start, end);
    assert forall |i: int| 0 <= i && i < sub.len() as int implies
        (sub[i] == '0' || sub[i] == '1') by {
        assert(sub[i] == s[start + i]);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    
    // Check if input is a valid bit string
    let mut valid = true;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            valid == (forall |j: int| 0 <= j && j < i ==> 
                (s@[j] == '0' || s@[j] == '1')),
    {
        if s[i] != '0' && s[i] != '1' {
            valid = false;
        }
        i = i + 1;
    }
    
    if !valid || s.len() == 0 {
        // Return "0" for invalid or empty input
        result.push('0');
        assert(result@.len() == 1);
        assert(result@[0] == '0');
        assert(ValidBitString(result@));
        return result;
    }
    
    assert(ValidBitString(s@));
    
    // Find first non-zero position
    let mut start = 0;
    while start < s.len() && s[start] == '0'
        invariant
            0 <= start <= s.len(),
            forall |j: int| 0 <= j && j < start ==> s@[j] == '0',
    {
        start = start + 1;
    }
    
    if start == s.len() {
        // All zeros, return "0"
        result.push('0');
        assert(result@.len() == 1);
        assert(result@[0] == '0');
        assert(ValidBitString(result@));
        
        // Prove Str2Int preservation
        proof {
            let mut k: int = 0;
            while k < s.len() as int
                invariant
                    0 <= k <= s.len() as int,
                    forall |j: int| 0 <= j && j < k ==> s@[j] == '0',
                    Str2Int(s@.subrange(k, s@.len() as int)) == 0,
            {
                if k < s.len() as int {
                    assert(s@[k] == '0');
                    let sub = s@.subrange(k, s@.len() as int);
                    if sub.len() > 0 {
                        lemma_valid_subrange(s@, k, s@.len() as int);
                        lemma_str2int_zero_prefix(sub);
                    }
                }
                k = k + 1;
            }
            assert(Str2Int(s@) == 0);
            assert(Str2Int(result@) == 0);
        }
        
        return result;
    }
    
    // Copy from start position to end
    let mut j = start;
    while j < s.len()
        invariant
            start <= j <= s.len(),
            result@.len() == (j - start) as int,
            forall |k: int| 0 <= k && k < result@.len() as int ==>
                result@[k] == s@[(start as int) + k],
            ValidBitString(result@),
    {
        result.push(s[j]);
        j = j + 1;
    }
    
    assert(result@.len() > 0);
    assert(result@.len() > 1 ==> result@[0] != '0') by {
        if result@.len() > 1 {
            assert(result@[0] == s@[start as int]);
            assert(s@[start as int] != '0');
        }
    }
    
    // Prove Str2Int preservation
    proof {
        let mut k: int = 0;
        while k < start as int
            invariant
                0 <= k <= start as int,
                forall |j: int| 0 <= j && j < k ==> s@[j] == '0',
                Str2Int(s@.subrange(k, s@.len() as int)) == Str2Int(result@),
        {
            if k < start as int {
                assert(s@[k] == '0');
                let sub = s@.subrange(k, s@.len() as int);
                lemma_valid_subrange(s@, k, s@.len() as int);
                lemma_str2int_zero_prefix(sub);
            }
            k = k + 1;
        }
        assert(s@.subrange(start as int, s@.len() as int) =~= result@);
        assert(Str2Int(s@) == Str2Int(result@));
    }
    
    result
}
// </vc-code>

fn main() {}
}