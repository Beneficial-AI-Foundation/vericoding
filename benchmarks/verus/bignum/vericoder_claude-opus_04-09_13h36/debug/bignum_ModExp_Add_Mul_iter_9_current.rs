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

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
    let sub = s.subrange(start, end);
    assert forall |i: int| 0 <= i && i < sub.len() implies 
        (sub.index(i) == '0' || sub.index(i) == '1') by {
        assert(sub.index(i) == s.index(start + i));
    }
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
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
    
    proof {
        lemma_valid_bit_string_subrange(s1@, 0, 0);
        lemma_valid_bit_string_subrange(s2@, 0, 0);
        lemma_str2int_empty();
    }
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant
            carry <= 1,
            ValidBitString(result@),
            i <= s1.len(),
            i <= s2.len(),
            ValidBitString(s1@),
            ValidBitString(s2@),
            ValidBitString(s1@.subrange(0, i as int)),
            ValidBitString(s2@.subrange(0, i as int)),
            Str2Int(result@) + carry as nat == 
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int))
        decreases
            if i < s1.len() { s1.len() - i } else { 0 } +
            if i < s2.len() { s2.len() - i } else { 0 } +
            carry as usize
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
        let new_carry = sum / 2;
        
        proof {
            let old_s1 = s1@.subrange(0, i as int);
            let old_s2 = s2@.subrange(0, i as int);
            let old_result = result@;
            
            lemma_valid_bit_string_push(result@, new_bit);
            
            let new_s1_range = if i < s1.len() { (i + 1) as int } else { i as int };
            let new_s2_range = if i < s2.len() { (i + 1) as int } else { i as int };
            
            if i < s1.len() {
                assert(0 <= 0);
                assert(0 <= new_s1_range);
                assert(new_s1_range <= s1@.len());
                lemma_valid_bit_string_subrange(s1@, 0, new_s1_range);
                assert(s1@.subrange(0, new_s1_range).len() == new_s1_range);
                assert(s1@.subrange(0, new_s1_range).subrange(0, i as int) == old_s1);
                assert(s1@.subrange(0, new_s1_range).index(i as int) == s1@[i as int]);
                assert(Str2Int(s1@.subrange(0, new_s1_range)) == 
                    2 * Str2Int(old_s1) + bit1 as nat);
            } else {
                assert(new_s1_range == i as int);
                assert(0 <= 0);
                assert(0 <= new_s1_range);
                assert(new_s1_range <= s1@.len());
                lemma_valid_bit_string_subrange(s1@, 0, new_s1_range);
                assert(s1@.subrange(0, new_s1_range) == old_s1);
                assert(Str2Int(s1@.subrange(0, new_s1_range)) == Str2Int(old_s1));
                assert(bit1 == 0);
            }
            
            if i < s2.len() {
                assert(0 <= 0);
                assert(0 <= new_s2_range);
                assert(new_s2_range <= s2@.len());
                lemma_valid_bit_string_subrange(s2@, 0, new_s2_range);
                assert(s2@.subrange(0, new_s2_range).len() == new_s2_range);
                assert(s2@.subrange(0, new_s2_range).subrange(0, i as int) == old_s2);
                assert(s2@.subrange(0, new_s2_range).index(i as int) == s2@[i as int]);
                assert(Str2Int(s2@.subrange(0, new_s2_range)) == 
                    2 * Str2Int(old_s2) + bit2 as nat);
            } else {
                assert(new_s2_range == i as int);
                assert(0 <= 0);
                assert(0 <= new_s2_range);
                assert(new_s2_range <= s2@.len());
                lemma_valid_bit_string_subrange(s2@, 0, new_s2_range);
                assert(s2@.subrange(0, new_s2_range) == old_s2);
                assert(Str2Int(s2@.subrange(0, new_s2_range)) == Str2Int(old_s2));
                assert(bit2 == 0);
            }
            
            lemma_str2int_append_bit(old_result, new_bit);
            
            assert(sum as nat == bit1 as nat + bit2 as nat + carry as nat);
            assert(new_carry as nat * 2 + (if new_bit == '1' { 1nat } else { 0nat }) == sum as nat);
            
            assert(Str2Int(old_result.push(new_bit)) + new_carry as nat ==
                   2 * Str2Int(old_s1) + bit1 as nat + 2 * Str2Int(old_s2) + bit2 as nat);
        }
        
        result.push(new_bit);
        carry = new_carry;
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