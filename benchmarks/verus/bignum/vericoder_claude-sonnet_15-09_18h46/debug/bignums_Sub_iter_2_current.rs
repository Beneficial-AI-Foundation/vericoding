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
{
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1,
{
}

/* helper modified by LLM (iteration 2): added decreases clause to while loop */
exec fn remove_leading_zeros(s: Vec<char>) -> (res: Vec<char>)
    requires ValidBitString(s@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@),
        res.len() > 0,
{
    let mut result = s;
    while result.len() > 1 && result[0] == '0'
        invariant
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s@),
            result.len() > 0,
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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::<char>::new();
    let mut borrow = 0;
    let mut i = s1.len();
    let mut j = s2.len();
    
    while i > 0 || j > 0
        invariant
            i <= s1.len(),
            j <= s2.len(),
            borrow == 0 || borrow == 1,
            ValidBitString(result@),
        decreases i + j,
    {
        let bit1 = if i > 0 {
            i = i - 1;
            if s1[i] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let bit2 = if j > 0 {
            j = j - 1;
            if s2[j] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let diff = bit1 - bit2 - borrow;
        
        if diff >= 0 {
            result.insert(0, if diff == 1 { '1' } else { '0' });
            borrow = 0;
        } else {
            result.insert(0, '1');
            borrow = 1;
        }
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    remove_leading_zeros(result)
}
// </vc-code>

fn main() {}
}


