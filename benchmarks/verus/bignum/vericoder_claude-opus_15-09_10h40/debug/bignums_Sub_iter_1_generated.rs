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

proof fn lemma_str2int_zero(n: nat)
    ensures
        Str2Int(Seq::new(n, |_| '0')) == 0,
    decreases n,
{
    if n == 0 {
        assert(Seq::new(0, |_| '0').len() == 0);
    } else {
        let s = Seq::new(n, |_| '0');
        assert(s.len() == n);
        assert(s.index(s.len() as int - 1) == '0');
        assert(s.subrange(0, s.len() as int - 1) == Seq::new(n - 1, |_| '0'));
        lemma_str2int_zero((n - 1) as nat);
    }
}

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
    let mut borrow = false;
    let mut i: usize = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if s1@.len() > s2@.len() { s1@.len() } else { s2@.len() },
            ValidBitString(result@),
            result@.len() == i,
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
        
        result.push(if diff == 1 { '1' } else { '0' });
        i = i + 1;
    }
    
    while result.len() > 1 && result[result.len() - 1] == '0'
        invariant
            ValidBitString(result@),
            result@.len() >= 1,
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
    binary_subtract(s1, s2)
}
// </vc-code>

fn main() {}
}


