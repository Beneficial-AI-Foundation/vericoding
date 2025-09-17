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
proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat },
{
    let s_new = s.push(c);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == c);
}

/* helper modified by LLM (iteration 5): fixed binary_subtract implementation */
exec fn binary_subtract(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
        Str2Int(s1@) >= Str2Int(s2@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@),
{
    let mut result = Vec::new();
    result.push('0');  // Initialize with at least one bit
    
    let mut borrow = false;
    let mut i: usize = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if s1@.len() > s2@.len() { s1@.len() } else { s2@.len() },
            ValidBitString(result@),
            result@.len() >= 1,
        decreases max_len - i
    {
        let bit1 = if i < s1.len() {
            if s1[i] == '1' { 1u8 } else { 0u8 }
        } else {
            0u8
        };
        
        let bit2 = if i < s2.len() {
            if s2[i] == '1' { 1u8 } else { 0u8 }
        } else {
            0u8
        };
        
        let mut diff = bit1;
        if borrow {
            if diff == 0 {
                diff = 1;
            } else {
                diff = 0;
                borrow = false;
            }
        }
        
        if diff < bit2 {
            diff = diff + 2;
            borrow = true;
        }
        diff = diff - bit2;
        
        if i == 0 {
            result[0] = if diff == 1 { '1' } else { '0' };
        } else {
            result.push(if diff == 1 { '1' } else { '0' });
        }
        i = i + 1;
    }
    
    while result.len() > 1 && result[result.len() - 1] == '0'
        invariant
            ValidBitString(result@),
            result@.len() >= 1,
        decreases result.len()
    {
        result.pop();
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
    /* code modified by LLM (iteration 5): calling binary_subtract helper */
    binary_subtract(s1, s2)
}
// </vc-code>

fn main() {}
}


