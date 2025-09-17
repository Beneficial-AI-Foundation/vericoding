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
/* helper modified by LLM (iteration 3): fixed type annotations and arithmetic operations */
proof fn lemma_str2int_subrange(s: Seq<char>, start: int, end: int)
    requires
        ValidBitString(s),
        0 <= start <= end <= s.len()
    ensures
        ValidBitString(s.subrange(start, end))
{
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() < s2.len()
    ensures
        Str2Int(s1) <= Str2Int(s2)
{
}

spec fn binary_sub_helper(s1: Seq<char>, s2: Seq<char>, borrow: bool, pos: int) -> (Seq<char>, bool)
    recommends
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= pos < s1.len()
{
    let bit1: int = if s1.index(pos) == '1' { 1int } else { 0int };
    let bit2: int = if pos < s2.len() && s2.index(pos) == '1' { 1int } else { 0int };
    let borrow_val: int = if borrow { 1int } else { 0int };
    let diff: int = bit1 - bit2 - borrow_val;
    if diff >= 0 {
        (seq![if diff == 1 { '1' } else { '0' }], false)
    } else {
        (seq!['1'], true)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed integer literal type annotations */
{
    let mut result = Vec::<char>::new();
    let mut borrow = false;
    let len1 = s1.len();
    let len2 = s2.len();
    
    let mut i = 0;
    while i < len1
        invariant
            i <= len1,
            ValidBitString(result@)
    {
        let bit1: int = if s1[i] == '1' { 1int } else { 0int };
        let bit2: int = if i < len2 && s2[i] == '1' { 1int } else { 0int };
        let borrow_val: int = if borrow { 1int } else { 0int };
        
        let diff: int = bit1 - bit2 - borrow_val;
        
        if diff >= 0 {
            result.push(if diff == 1 { '1' } else { '0' });
            borrow = false;
        } else {
            result.push('1');
            borrow = true;
        }
        
        i += 1;
    }
    
    // Remove leading zeros
    while result.len() > 1 && result[result.len() - 1] == '0'
        invariant
            result.len() >= 1,
            ValidBitString(result@)
    {
        result.pop();
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}


