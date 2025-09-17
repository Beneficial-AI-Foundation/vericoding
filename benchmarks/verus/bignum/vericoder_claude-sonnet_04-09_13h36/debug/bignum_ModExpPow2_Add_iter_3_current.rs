use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires ValidBitString(s), bit == '0' || bit == '1'
    ensures ValidBitString(s.push(bit)),
            Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat })
{
    let extended = s.push(bit);
    assert(extended.len() == s.len() + 1);
    assert(extended.index(extended.len() as int - 1) == bit);
    assert(extended.subrange(0, extended.len() as int - 1) =~= s);
}

proof fn lemma_str2int_empty()
    ensures ValidBitString(seq![]), Str2Int(seq![]) == 0
{
}

proof fn lemma_valid_bit_string_slice(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
}

proof fn lemma_str2int_leading_zero(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0, s.index(0) == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 1 {
        assert(Str2Int(s) == 0);
        assert(s.subrange(1, 1).len() == 0);
        assert(Str2Int(s.subrange(1, 1)) == 0);
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(ValidBitString(tail)) by { lemma_valid_bit_string_slice(s, 1, s.len() as int); }
        assert(s.subrange(0, s.len() as int - 1) == seq!['0'].add(tail.subrange(0, tail.len() as int - 1)));
        lemma_str2int_leading_zero(tail);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            ValidBitString(result@.reverse()),
            carry <= 2,
            i1 <= s1.len(),
            i2 <= s2.len(),
            Str2Int(result@.reverse()) + carry as nat * Exp_int(2, result.len() as nat) 
                == Str2Int(s1@.subrange(i1 as int, s1.len() as int)) 
                 + Str2Int(s2@.subrange(i2 as int, s2.len() as int))
    {
        let bit1 = if i1 > 0 { 
            i1 -= 1; 
            if s1[i1] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let bit2 = if i2 > 0 { 
            i2 -= 1; 
            if s2[i2] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(result_bit);
        
        proof {
            assert(ValidBitString(result@.reverse())) by {
                assert(result_bit == '0' || result_bit == '1');
                lemma_valid_bit_string_slice(result@.reverse(), 0, result@.reverse().len() as int);
            }
        }
    }
    
    result.reverse();
    
    proof {
        assert(ValidBitString(result@));
        assert(i1 == 0 && i2 == 0 && carry == 0);
        assert(s1@.subrange(0, s1.len() as int) =~= s1@);
        assert(s2@.subrange(0, s2.len() as int) =~= s2@);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}