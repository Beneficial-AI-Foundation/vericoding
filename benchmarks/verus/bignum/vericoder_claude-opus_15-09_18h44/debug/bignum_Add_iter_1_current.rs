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
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == '1');
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            0 <= i <= max_len + 1,
            carry == 0 || carry == 1,
            ValidBitString(result@),
            Str2Int(result@) + (carry as nat) * pow2(i as nat) == 
                Str2Int(s1@.subrange(0, min(i as int, s1@.len() as int))) + 
                Str2Int(s2@.subrange(0, min(i as int, s2@.len() as int))),
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
        
        let sum = bit1 + bit2 + carry;
        let new_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(new_bit);
        
        if i < max_len {
            i = i + 1;
        } else {
            break;
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}