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
/* helper modified by LLM (iteration 9): Fixed pow2 assertion and completed str2int_relation proof */
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
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }),
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
        (s.index(start + i) == '0' || s.index(start + i) == '1') by {
            assert(s.subrange(start, end).index(i) == s.index(start + i));
            assert(s.index(start + i) == '0' || s.index(start + i) == '1');
        }
}

proof fn pow2_zero()
    ensures pow2(0nat) == 1nat
{
}

proof fn str2int_relation(s: Seq<char>, i: nat)
    requires ValidBitString(s),
        i <= s.len(),
    ensures Str2Int(s.subrange(0, i as int)) * pow2((s.len() - i) as nat) + 
            Str2Int(s.subrange(i as int, s.len() as int)) == Str2Int(s),
    decreases s.len() - i,
{
    if i == s.len() {
        assert(s.subrange(0, i as int) =~= s);
        assert(s.subrange(i as int, s.len() as int) =~= Seq::<char>::empty());
        pow2_zero();
        assert(pow2(0nat) == 1nat);
        assert(Str2Int(s.subrange(i as int, s.len() as int)) == 0);
        assert(Str2Int(s.subrange(0, i as int)) * 1 + 0 == Str2Int(s));
    } else {
        valid_bitstring_subrange(s, 0, i as int);
        valid_bitstring_subrange(s, i as int, s.len() as int);
        str2int_relation(s, i + 1);
        
        let left = s.subrange(0, i as int);
        let right = s.subrange(i as int, s.len() as int);
        let c = s.index(i as int);
        
        assert(right.len() > 0);
        assert(right.index(0) == c);
        assert(right.subrange(1, right.len() as int) =~= s.subrange((i + 1) as int, s.len() as int));
        
        assert(Str2Int(right) == 2 * Str2Int(right.subrange(0, right.len() as int - 1)) + 
               (if right.index(right.len() as int - 1) == '1' { 1nat } else { 0nat }));
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
    /* code modified by LLM (iteration 9): Fixed loop invariants and arithmetic overflow */
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
            forall|j: int| 0 <= j && j < i ==> result@.index(j) == '0' || result@.index(j) == '1',
            i > s1@.len() ==> carry == 0 || i == s1@.len() + 1,
            i > s2@.len() ==> carry == 0 || i == s2@.len() + 1,
            i > max_len ==> carry == 0,
        decreases if i >= max_len { 1 - carry } else { max_len - i + 1 }
    {
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
        
        proof {
            assert(new_bit == '0' || new_bit == '1');
            assert(ValidBitString(result@));
            assert(sum <= 3);
            assert(carry <= 1);
        }
        
        result.push(new_bit);
        
        proof {
            assert(result@.index(i as int) == new_bit);
            assert(ValidBitString(result@));
        }
        
        assert(i < usize::MAX);
        i = i + 1;
        
        proof {
            if i > max_len {
                assert(i == max_len + 1);
                assert(bit1 == 0);
                assert(bit2 == 0);
                assert(sum == carry);
                assert(carry == 0);
            }
        }
    }
    
    proof {
        assert(carry == 0);
        assert(i >= max_len);
        assert(ValidBitString(result@));
    }
    
    result
}
// </vc-code>

fn main() {}
}