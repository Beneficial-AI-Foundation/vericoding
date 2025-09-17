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
/* helper modified by LLM (iteration 5): Added proof lemmas for bit string properties */
use vstd::arithmetic::power2::pow2;
use vstd::math::min;

proof fn str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn str2int_append(s: Seq<char>, c: char)
    requires ValidBitString(s),
        c == '0' || c == '1',
    ensures ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == Str2Int(s) + (if c == '1' { pow2(s.len() as nat) } else { 0 }),
{
    assert(s.push(c).len() == s.len() + 1);
    assert(s.push(c).subrange(0, s.len() as int) =~= s);
    assert(s.push(c).index(s.len() as int) == c);
}

proof fn valid_bitstring_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s),
        0 <= start <= end <= s.len(),
    ensures ValidBitString(s.subrange(start, end)),
{
    assert forall|i: int| 0 <= i && i < (end - start) implies
        s.subrange(start, end).index(i) == s.index(start + i) &&
        (s.index(start + i) == '0' || s.index(start + i) == '1');
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
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and invariant issues */
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    proof {
        str2int_empty();
        assert(result@ =~= Seq::<char>::empty());
        assert(Str2Int(result@) == 0);
    }
    
    while i < max_len || carry > 0
        invariant
            0 <= i,
            i <= max_len + 1,
            carry == 0 || carry == 1,
            ValidBitString(result@),
            result@.len() == i,
            i <= s1@.len() ==> ValidBitString(s1@.subrange(0, i as int)),
            i <= s2@.len() ==> ValidBitString(s2@.subrange(0, i as int)),
            Str2Int(result@) + (carry as nat) * pow2(i as nat) == 
                Str2Int(if i <= s1@.len() { s1@.subrange(0, i as int) } else { s1@ }) + 
                Str2Int(if i <= s2@.len() { s2@.subrange(0, i as int) } else { s2@ }),
        decreases if i >= max_len { 1 - carry } else { max_len - i + 1 }
    {
        proof {
            if i < s1@.len() {
                valid_bitstring_subrange(s1@, 0, (i + 1) as int);
            }
            if i < s2@.len() {
                valid_bitstring_subrange(s2@, 0, (i + 1) as int);
            }
        }
        
        let bit1: u8 = if i < s1.len() {
            if s1[i] == '1' { 1 } else { 0 }
        } else {
            0
        };
        
        let bit2: u8 = if i < s2.len() {
            if s2[i] == '1' { 1 } else { 0 }
        } else {
            0
        };
        
        let sum: u8 = bit1 + bit2 + carry;
        let new_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(new_bit);
        
        proof {
            str2int_append(result@.subrange(0, i as int), new_bit);
            assert(result@.subrange(0, (i + 1) as int) =~= result@);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(carry == 0);
        assert(i >= max_len);
        assert(result@.len() >= max_len);
        assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}