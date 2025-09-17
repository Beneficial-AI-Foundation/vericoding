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
use vstd::arithmetic::power2::*;

proof fn str2int_append_bit(s: Seq<char>, bit: char)
    requires 
        ValidBitString(s),
        bit == '0' || bit == '1',
    ensures 
        ValidBitString(s.push(bit)),
        Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat }),
    decreases s.len(),
{
    assert(s.push(bit).len() == s.len() + 1);
    assert(s.push(bit).subrange(0, s.len() as int) =~= s);
    assert(s.push(bit).index(s.len() as int) == bit);
}

proof fn str2int_zero()
    ensures Str2Int(Seq::<char>::empty()) == 0,
{
}

proof fn valid_bit_string_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures ValidBitString(s.push(c)),
{
    assert forall |i: int| 0 <= i && i < s.push(c).len() as int implies
        s.push(c).index(i) == '0' || s.push(c).index(i) == '1'
    by {
        if i < s.len() as int {
            assert(s.push(c).index(i) == s.index(i));
        } else {
            assert(i == s.len() as int);
            assert(s.push(c).index(i) == c);
        }
    }
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
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if len1 >= len2 { len1 } else { len2 },
            carry <= 1,
            ValidBitString(result@),
            Str2Int(result@) + (carry as nat) * pow2(i as nat) == 
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int)),
    {
        let bit1: u8 = if i < len1 {
            if s1[i] == '1' { 1 } else { 0 }
        } else {
            0
        };
        
        let bit2: u8 = if i < len2 {
            if s2[i] == '1' { 1 } else { 0 }
        } else {
            0
        };
        
        let sum = bit1 + bit2 + carry;
        let new_bit = if (sum & 1) == 1 { '1' } else { '0' };
        carry = sum >> 1;
        
        proof {
            if i < len1 {
                assert(s1@.subrange(0, (i + 1) as int) =~= 
                       s1@.subrange(0, i as int).push(s1@.index(i as int)));
                str2int_append_bit(s1@.subrange(0, i as int), s1@.index(i as int));
            } else {
                assert(s1@.subrange(0, (i + 1) as int) =~= s1@.subrange(0, i as int));
            }
            
            if i < len2 {
                assert(s2@.subrange(0, (i + 1) as int) =~= 
                       s2@.subrange(0, i as int).push(s2@.index(i as int)));
                str2int_append_bit(s2@.subrange(0, i as int), s2@.index(i as int));
            } else {
                assert(s2@.subrange(0, (i + 1) as int) =~= s2@.subrange(0, i as int));
            }
            
            valid_bit_string_push(result@, new_bit);
            str2int_append_bit(result@, new_bit);
            
            assert(pow2((i + 1) as nat) == 2 * pow2(i as nat)) by {
                lemma_pow2_unfold((i + 1) as nat);
            }
        }
        
        result.push(new_bit);
        i = i + 1;
    }
    
    if carry == 1 {
        proof {
            valid_bit_string_push(result@, '1');
            str2int_append_bit(result@, '1');
            assert(s1@.subrange(0, len1 as int) =~= s1@);
            assert(s2@.subrange(0, len2 as int) =~= s2@);
        }
        result.push('1');
    } else {
        proof {
            assert(s1@.subrange(0, len1 as int) =~= s1@);
            assert(s2@.subrange(0, len2 as int) =~= s2@);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}