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

/* helper modified by LLM (iteration 8): ensuring proper value preservation */
exec fn remove_leading_zeros(s: Vec<char>) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
        s.len() > 0,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@),
        res.len() > 0,
{
    if s.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = s;
    
    while result.len() > 1 && result[0] == '0'
        invariant
            ValidBitString(result@),
            result.len() > 0,
            Str2Int(result@) == Str2Int(s@),
        decreases result.len(),
    {
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
    /* code modified by LLM (iteration 8): implementing proper binary subtraction algorithm */
    let len1 = s1.len();
    let len2 = s2.len();
    
    if len1 == 0 && len2 == 0 {
        return vec!['0'];
    }
    
    if len2 == 0 || (len2 == 1 && s2[0] == '0') {
        let mut result = s1.to_vec();
        if result.len() == 0 {
            result.push('0');
        }
        return remove_leading_zeros(result);
    }
    
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut result = Vec::<char>::new();
    let mut borrow = 0;
    
    let mut idx = 0;
    while idx < max_len
        invariant
            idx <= max_len,
            borrow == 0 || borrow == 1,
            ValidBitString(result@),
            max_len == if len1 > len2 { len1 } else { len2 },
            len1 == s1@.len(),
            len2 == s2@.len(),
        decreases max_len - idx,
    {
        let bit1 = if idx < len1 {
            let pos1 = len1 - 1 - idx;
            if s1[pos1] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let bit2 = if idx < len2 {
            let pos2 = len2 - 1 - idx;
            if s2[pos2] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let mut diff = bit1 - bit2 - borrow;
        
        if diff < 0 {
            diff = diff + 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        
        result.insert(0, if diff == 1 { '1' } else { '0' });
        idx = idx + 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    remove_leading_zeros(result)
}
// </vc-code>

fn main() {}
}


