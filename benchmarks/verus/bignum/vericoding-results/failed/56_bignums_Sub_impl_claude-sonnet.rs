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
proof fn lemma_str2int_subrange(s: Seq<char>, start: int, end: int)
    requires
        ValidBitString(s),
        0 <= start <= end <= s.len(),
    ensures
        ValidBitString(s.subrange(start, end)),
{
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0,
{
}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0,
    decreases 1nat,
{
    let s = seq!['0'];
    assert(s.len() == 1);
    assert(s.index(0) == '0');
    assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, 0)) + 0);
    assert(s.subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(Seq::<char>::empty()) == 0);
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1,
    decreases 1nat,
{
    let s = seq!['1'];
    assert(s.len() == 1);
    assert(s.index(0) == '1');
    assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, 0)) + 1);
    assert(s.subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(Seq::<char>::empty()) == 0);
}

/* helper modified by LLM (iteration 10): preserving Str2Int value while removing leading zeros */
exec fn remove_leading_zeros(s: Vec<char>) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
        s.len() > 0,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@),
        res.len() > 0,
{
    let mut result = s;
    
    while result.len() > 1 && result[0] == '0'
        invariant
            ValidBitString(result@),
            result.len() > 0,
            Str2Int(result@) == Str2Int(s@),
        decreases result.len(),
    {
        proof {
            let old_result = result@;
            let new_result = old_result.subrange(1, old_result.len() as int);
            if old_result.len() > 1 && old_result[0] == '0' {
                assert(Str2Int(old_result) == 2 * Str2Int(old_result.subrange(0, old_result.len() as int - 1)) + if old_result[old_result.len() as int - 1] == '1' { 1 } else { 0 });
                assert(old_result.subrange(0, old_result.len() as int - 1) == (seq!['0'] + new_result.subrange(0, new_result.len() as int - 1)));
            }
        }
        result.remove(0);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): implementing binary subtraction with proper arithmetic */
    let len1 = s1.len();
    let len2 = s2.len();
    
    if len2 == 0 || (len2 == 1 && s2[0] == '0') {
        let mut result = Vec::<char>::new();
        let mut i = 0;
        while i < len1
            invariant
                i <= len1,
                len1 == s1@.len(),
                ValidBitString(result@),
                result@.len() == i,
                forall |j: int| 0 <= j < i ==> result@[j] == s1@[j],
            decreases len1 - i,
        {
            result.push(s1[i]);
            i = i + 1;
        }
        
        if result.len() == 0 {
            result.push('0');
        }
        
        proof {
            assert(Str2Int(result@) == Str2Int(s1@));
            assert(Str2Int(s2@) == 0);
        }
        
        return remove_leading_zeros(result);
    }
    
    if Str2Int(s1@) == Str2Int(s2@) {
        return vec!['0'];
    }
    
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut result = Vec::<char>::new();
    
    let mut s1_val = Str2Int(s1@);
    let s2_val = Str2Int(s2@);
    let diff = s1_val - s2_val;
    
    if diff == 0 {
        return vec!['0'];
    }
    
    let mut temp_diff = diff;
    
    while temp_diff > 0
        invariant
            ValidBitString(result@),
            temp_diff < diff + 1,
        decreases temp_diff,
    {
        if temp_diff % 2 == 1 {
            result.insert(0, '1');
        } else {
            result.insert(0, '0');
        }
        temp_diff = temp_diff / 2;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    proof {
        assert(Str2Int(result@) == diff);
        assert(diff == Str2Int(s1@) - Str2Int(s2@));
    }
    
    remove_leading_zeros(result)
}
// </vc-code>

fn main() {}
}


