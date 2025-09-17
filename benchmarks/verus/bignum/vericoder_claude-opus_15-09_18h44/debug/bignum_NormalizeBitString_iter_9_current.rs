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
/* helper modified by LLM (iteration 9): Add lemmas to prove Str2Int equality */
proof fn lemma_str2int_zeros(s: Seq<char>)
    requires
        ValidBitString(s),
        forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0',
    ensures
        Str2Int(s) == 0,
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
    } else {
        lemma_str2int_zeros(s.subrange(0, s.len() - 1));
        assert(s[s.len() - 1] == '0');
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() - 1)) + 0);
        assert(Str2Int(s.subrange(0, s.len() - 1)) == 0);
        assert(Str2Int(s) == 0);
    }
}

proof fn lemma_str2int_suffix(s: Seq<char>, start: int)
    requires
        0 <= start < s.len(),
        ValidBitString(s),
        forall |i: int| 0 <= i && i < start ==> s[i] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(start, s.len() as int)),
    decreases s.len()
{
    if start == 0 {
        assert(s.subrange(start, s.len() as int) =~= s);
    } else {
        assert(s[0] == '0');
        let s_tail = s.subrange(1, s.len() as int);
        assert(ValidBitString(s_tail));
        assert(forall |i: int| 0 <= i && i < start - 1 ==> s_tail[i] == s[i + 1] == '0');
        lemma_str2int_suffix(s_tail, start - 1);
        assert(s_tail.subrange(start - 1, s_tail.len() as int) =~= s.subrange(start, s.len() as int));
        assert(Str2Int(s_tail) == Str2Int(s.subrange(start, s.len() as int)));
        
        // Now prove Str2Int(s) == Str2Int(s_tail)
        if s.len() == 1 {
            assert(s[0] == '0');
            assert(Str2Int(s) == 0);
            assert(s_tail.len() == 0);
            assert(Str2Int(s_tail) == 0);
        } else {
            assert(s.subrange(0, s.len() - 1).subrange(0, s.len() - 2) =~= s_tail.subrange(0, s_tail.len() - 1));
            assert(s[s.len() - 1] == s_tail[s_tail.len() - 1]);
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1 } else { 0 }));
            assert(Str2Int(s_tail) == 2 * Str2Int(s_tail.subrange(0, s_tail.len() - 1)) + (if s_tail[s_tail.len() - 1] == '1' { 1 } else { 0 }));
            lemma_str2int_leading_zero(s.subrange(0, s.len() - 1));
            assert(Str2Int(s.subrange(0, s.len() - 1)) == Str2Int(s_tail.subrange(0, s_tail.len() - 1)));
            assert(Str2Int(s) == Str2Int(s_tail));
        }
        assert(Str2Int(s) == Str2Int(s.subrange(start, s.len() as int)));
    }
}

proof fn lemma_str2int_leading_zero(s: Seq<char>)
    requires
        s.len() > 0,
        ValidBitString(s),
        s[0] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(1, s.len() as int)),
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == '0');
        assert(Str2Int(s) == 0);
        assert(s.subrange(1, s.len() as int).len() == 0);
        assert(Str2Int(s.subrange(1, s.len() as int)) == 0);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        assert(ValidBitString(s_tail));
        assert(s.subrange(0, s.len() - 1).subrange(0, s.len() - 2) =~= s_tail.subrange(0, s_tail.len() - 1));
        assert(s[s.len() - 1] == s_tail[s_tail.len() - 1]);
        lemma_str2int_leading_zero(s.subrange(0, s.len() - 1));
        assert(Str2Int(s.subrange(0, s.len() - 1)) == Str2Int(s.subrange(0, s.len() - 1).subrange(1, s.len() - 1)));
        assert(s.subrange(0, s.len() - 1).subrange(1, s.len() - 1) =~= s_tail.subrange(0, s_tail.len() - 1));
        assert(Str2Int(s) == 2 * Str2Int(s_tail.subrange(0, s_tail.len() - 1)) + (if s[s.len() - 1] == '1' { 1 } else { 0 }));
        assert(Str2Int(s_tail) == 2 * Str2Int(s_tail.subrange(0, s_tail.len() - 1)) + (if s_tail[s_tail.len() - 1] == '1' { 1 } else { 0 }));
        assert(Str2Int(s) == Str2Int(s_tail));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): use lemmas to prove Str2Int equality */
    let mut result = Vec::<char>::new();
    
    // Check if input is valid
    let mut is_valid = true;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_valid <==> forall |j: int| 0 <= j && j < i ==> (s@[j] == '0' || s@[j] == '1'),
        decreases s.len() - i
    {
        if s[i] != '0' && s[i] != '1' {
            is_valid = false;
        }
        i = i + 1;
    }
    
    if !is_valid || s.len() == 0 {
        // Invalid input or empty - return "0"
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            assert(ValidBitString(result@));
            assert(!is_valid || s.len() == 0);
            if is_valid && s.len() == 0 {
                assert(ValidBitString(s@));
                assert(Str2Int(s@) == 0);
                assert(Str2Int(result@) == 0);
            }
        }
        return result;
    }
    
    // Input is valid, find first non-zero
    let mut start_idx: usize = 0;
    let mut found_non_zero = false;
    let mut j: usize = 0;
    
    while j < s.len()
        invariant
            0 <= j <= s.len(),
            is_valid,
            ValidBitString(s@),
            !found_non_zero ==> forall |k: int| 0 <= k && k < j ==> s@[k] == '0',
            found_non_zero ==> start_idx < s.len() && s@[start_idx as int] == '1',
            found_non_zero ==> start_idx <= j,
            found_non_zero ==> forall |k: int| 0 <= k && k < start_idx ==> s@[k] == '0',
        decreases s.len() - j
    {
        if s[j] == '1' {
            if !found_non_zero {
                start_idx = j;
                found_non_zero = true;
            }
        }
        j = j + 1;
    }
    
    if !found_non_zero {
        // All zeros
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            assert(ValidBitString(result@));
            assert(forall |k: int| 0 <= k && k < s@.len() ==> s@[k] == '0');
            lemma_str2int_zeros(s@);
            assert(Str2Int(s@) == 0);
            assert(Str2Int(result@) == 0);
        }
    } else {
        // Copy from start_idx to end
        let mut k: usize = start_idx;
        while k < s.len()
            invariant
                start_idx <= k <= s.len(),
                ValidBitString(s@),
                result@.len() == k - start_idx,
                forall |m: int| 0 <= m && m < result@.len() ==> result@[m] == s@[start_idx as int + m],
                forall |m: int| 0 <= m && m < result@.len() ==> (result@[m] == '0' || result@[m] == '1'),
                result@.len() > 0 ==> result@[0] == s@[start_idx as int],
                s@[start_idx as int] == '1',
                result@.len() > 0 ==> result@[0] == '1',
                result@ =~= s@.subrange(start_idx as int, k as int),
            decreases s.len() - k
        {
            result.push(s[k]);
            k = k + 1;
        }
        
        proof {
            assert(ValidBitString(result@));
            assert(result@[0] == '1');
            assert(result@[0] != '0');
            assert(result@ =~= s@.subrange(start_idx as int, s@.len() as int));
            assert(forall |m: int| 0 <= m && m < start_idx ==> s@[m] == '0');
            lemma_str2int_suffix(s@, start_idx as int);
            assert(Str2Int(s@) == Str2Int(s@.subrange(start_idx as int, s@.len() as int)));
            assert(Str2Int(s@) == Str2Int(result@));
        }
    }
    
    proof {
        assert(result@.len() > 0);
        assert(ValidBitString(result@));
        if result@.len() > 1 {
            assert(result@[0] != '0');
        }
        assert(ValidBitString(s@) ==> Str2Int(s@) == Str2Int(result@));
    }
    
    result
}
// </vc-code>

fn main() {}
}


