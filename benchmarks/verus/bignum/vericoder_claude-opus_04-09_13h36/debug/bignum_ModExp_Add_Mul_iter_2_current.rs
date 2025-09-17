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
    ensures Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat })
    decreases s.len()
{
    let s_new = s.push(bit);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() - 1) == s);
    assert(s_new.index(s_new.len() - 1) == bit);
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
    let s_new = s.push(c);
    assert forall |i: int| 0 <= i && i < s_new.len() implies 
        (s_new.index(i) == '0' || s_new.index(i) == '1') by {
        if i < s.len() {
            assert(s_new.index(i) == s.index(i));
        } else {
            assert(i == s.len());
            assert(s_new.index(i) == c);
        }
    }
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_add_with_carry(s1: Seq<char>, s2: Seq<char>, carry: u8, result: Seq<char>, bit: char, new_carry: u8)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        ValidBitString(result),
        carry <= 1,
        new_carry <= 1,
        bit == '0' || bit == '1',
        Str2Int(result) + carry as nat == Str2Int(s1) + Str2Int(s2),
        new_carry as nat * 2 + (if bit == '1' { 1nat } else { 0nat }) == 
            (if s1.len() > 0 { if s1.last() == '1' { 1nat } else { 0nat } } else { 0nat }) +
            (if s2.len() > 0 { if s2.last() == '1' { 1nat } else { 0nat } } else { 0nat }) +
            carry as nat
    ensures 
        Str2Int(result.push(bit)) + new_carry as nat == Str2Int(s1) + Str2Int(s2)
{
    lemma_str2int_append_bit(result, bit);
    
    if s1.len() > 0 {
        assert(s1.index(s1.len() - 1) == s1.last());
    }
    if s2.len() > 0 {
        assert(s2.index(s2.len() - 1) == s2.last());
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
    let mut i: usize = 0;
    let mut carry: u8 = 0;
    let mut result = Vec::<char>::new();
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant
            carry <= 1,
            ValidBitString(result@),
            i <= s1.len(),
            i <= s2.len(),
            Str2Int(result@) + carry as nat == 
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int))
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
        
        proof {
            lemma_valid_bit_string_push(result@, new_bit);
            
            let old_s1 = s1@.subrange(0, i as int);
            let old_s2 = s2@.subrange(0, i as int);
            
            if i < s1.len() {
                assert(s1@.subrange(0, (i + 1) as int).len() == (i + 1) as int);
                assert(s1@.subrange(0, (i + 1) as int).subrange(0, i as int) == old_s1);
                assert(s1@.subrange(0, (i + 1) as int).index(i as int) == s1@[i as int]);
                assert(Str2Int(s1@.subrange(0, (i + 1) as int)) == 
                    2 * Str2Int(old_s1) + bit1 as nat);
            }
            
            if i < s2.len() {
                assert(s2@.subrange(0, (i + 1) as int).len() == (i + 1) as int);
                assert(s2@.subrange(0, (i + 1) as int).subrange(0, i as int) == old_s2);
                assert(s2@.subrange(0, (i + 1) as int).index(i as int) == s2@[i as int]);
                assert(Str2Int(s2@.subrange(0, (i + 1) as int)) == 
                    2 * Str2Int(old_s2) + bit2 as nat);
            }
            
            lemma_str2int_append_bit(result@, new_bit);
            
            assert(2 * (Str2Int(result@) + (carry as nat)) + (if new_bit == '1' { 1nat } else { 0nat }) ==
                   2 * Str2Int(old_s1) + bit1 as nat + 2 * Str2Int(old_s2) + bit2 as nat);
        }
        
        result.push(new_bit);
        i = i + 1;
    }
    
    proof {
        assert(i >= s1.len());
        assert(i >= s2.len());
        assert(s1@.subrange(0, i as int) == s1@);
        assert(s2@.subrange(0, i as int) == s2@);
        assert(carry == 0);
    }
    
    result
}
// </vc-code>

fn main() {}
}