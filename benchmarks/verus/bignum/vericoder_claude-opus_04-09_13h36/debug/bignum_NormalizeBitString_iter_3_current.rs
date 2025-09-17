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
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
    decreases s.len()
{
    let s_zero = s.push('0');
    assert(s_zero.len() == s.len() + 1);
    assert(s_zero.subrange(0, s_zero.len() as int - 1) =~= s);
    assert(s_zero.index(s_zero.len() as int - 1) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    let s_one = s.push('1');
    assert(s_one.len() == s.len() + 1);
    assert(s_one.subrange(0, s_one.len() as int - 1) =~= s);
    assert(s_one.index(s_one.len() as int - 1) == '1');
}

proof fn lemma_str2int_leading_zero(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0, s[0] == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 1 {
        assert(s =~= seq!['0']);
        assert(Str2Int(s) == 0);
        assert(s.subrange(1, s.len() as int) =~= Seq::<char>::empty());
        assert(Str2Int(Seq::<char>::empty()) == 0);
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(ValidBitString(tail)) by {
            assert forall |i: int| 0 <= i && i < tail.len() as int implies
                tail[i] == '0' || tail[i] == '1' by {
                assert(tail[i] == s[i + 1]);
            }
        }
        
        let s_minus_last = s.subrange(0, s.len() as int - 1);
        let tail_minus_last = tail.subrange(0, tail.len() as int - 1);
        
        assert(s_minus_last[0] == '0');
        assert(s_minus_last.subrange(1, s_minus_last.len() as int) =~= tail_minus_last);
        
        lemma_str2int_leading_zero(s_minus_last);
        
        let last_bit = if s[s.len() as int - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(s_minus_last) + last_bit);
        assert(Str2Int(tail) == 2 * Str2Int(tail_minus_last) + last_bit);
        assert(Str2Int(s_minus_last) == Str2Int(tail_minus_last));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    
    // Check if input is a valid bit string
    let mut is_valid = true;
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len(),
                  is_valid == (forall |j: int| 0 <= j && j < i ==> s@[j] == '0' || s@[j] == '1')
    {
        if s[i] != '0' && s[i] != '1' {
            is_valid = false;
        }
        i = i + 1;
    }
    
    if !is_valid || s.len() == 0 {
        // Return "0" for invalid or empty input
        result.push('0');
        assert(result@.len() == 1);
        assert(result@[0] == '0');
        assert(ValidBitString(result@));
        return result;
    }
    
    assert(ValidBitString(s@));
    
    // Find first non-zero character
    let mut first_one = s.len();
    let mut j = 0;
    while j < s.len()
        invariant 0 <= j <= s.len(),
                  first_one == s.len(),
                  forall |k: int| 0 <= k && k < j ==> s@[k] == '0'
    {
        if s[j] == '1' {
            first_one = j;
            break;
        }
        j = j + 1;
    }
    
    if first_one == s.len() {
        // All zeros
        result.push('0');
        assert(result@.len() == 1);
        assert(result@[0] == '0');
        assert(ValidBitString(result@));
        
        // Prove value preservation
        assert(ValidBitString(s@));
        assert forall |k: int| 0 <= k && k < s@.len() implies s@[k] == '0' by {
            if 0 <= k && k < j {
                // covered by loop invariant
            } else if j <= k && k < s@.len() {
                assert(first_one == s.len());
                assert(s@[k] != '1');
                assert(s@[k] == '0' || s@[k] == '1');
            }
        }
        
        proof {
            let mut idx: int = s@.len() as int;
            while idx > 0
                invariant 0 <= idx <= s@.len(),
                          Str2Int(s@.subrange(idx, s@.len() as int)) == 0
            {
                idx = idx - 1;
                let sub = s@.subrange(idx, s@.len() as int);
                assert(sub.len() > 0);
                assert(sub[sub.len() as int - 1] == s@[s@.len() as int - 1]);
                assert(s@[s@.len() as int - 1] == '0');
                
                if sub.len() == 1 {
                    assert(Str2Int(sub) == 0);
                } else {
                    let sub_minus_last = sub.subrange(0, sub.len() as int - 1);
                    assert(sub_minus_last =~= s@.subrange(idx, s@.len() as int - 1));
                    assert(Str2Int(sub) == 2 * Str2Int(sub_minus_last) + 0);
                    assert(Str2Int(sub_minus_last) == 0);
                }
            }
            assert(Str2Int(s@) == 0);
        }
        assert(Str2Int(result@) == 0);
        
        return result;
    }
    
    // Copy from first_one to end
    let mut k = first_one;
    while k < s.len()
        invariant first_one <= k <= s.len(),
                  result@.len() == (k - first_one) as nat,
                  forall |m: int| 0 <= m && m < result@.len() ==> result@[m] == s@[(first_one as int) + m],
                  ValidBitString(result@)
    {
        result.push(s[k]);
        k = k + 1;
    }
    
    assert(result@.len() > 0);
    assert(result@[0] == s@[first_one as int]);
    assert(s@[first_one as int] == '1');
    assert(result@.len() > 1 ==> result@[0] != '0');
    
    // Prove value preservation
    proof {
        let mut idx: int = 0;
        while idx < first_one as int
            invariant 0 <= idx <= first_one as int,
                      Str2Int(s@.subrange(idx, s@.len() as int)) == Str2Int(s@.subrange(first_one as int, s@.len() as int))
        {
            assert(s@[idx] == '0');
            lemma_str2int_leading_zero(s@.subrange(idx, s@.len() as int));
            idx = idx + 1;
        }
        assert(result@ =~= s@.subrange(first_one as int, s@.len() as int));
        assert(Str2Int(s@) == Str2Int(result@));
    }
    
    return result;
}
// </vc-code>

fn main() {}
}