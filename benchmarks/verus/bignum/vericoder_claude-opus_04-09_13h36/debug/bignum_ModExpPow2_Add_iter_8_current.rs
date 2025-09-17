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
    let new_s = s.push(bit);
    assert(new_s.len() == s.len() + 1);
    assert(new_s.subrange(0, new_s.len() as int - 1) == s);
    assert(new_s.index(new_s.len() as int - 1) == bit);
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_valid_bitstring_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
    assert forall |i: int| 0 <= i && i < s.push(c).len() as int implies 
        s.push(c).index(i) == '0' || s.push(c).index(i) == '1' by {
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
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    
    while i < max_len || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 1,
            i <= max_len || (i == max_len + 1 && carry == 0),
            Str2Int(result@) + (carry as nat) * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, if i < len1 { i as int } else { len1 as int })) + 
                Str2Int(s2@.subrange(0, if i < len2 { i as int } else { len2 as int }))
        decreases
            if i < max_len { (max_len - i) as int + (carry as int) }
            else { carry as int }
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
            lemma_valid_bitstring_push(result@, new_bit);
            lemma_str2int_append_bit(result@, new_bit);
            
            if i < s1.len() {
                let next_idx = if (i + 1) as int <= len1 as int { (i + 1) as int } else { len1 as int };
                assert(s1@.subrange(0, next_idx) == s1@.subrange(0, i as int).push(s1@[i as int]));
                if s1@[i as int] == '1' {
                    lemma_str2int_append_bit(s1@.subrange(0, i as int), '1');
                } else {
                    lemma_str2int_append_bit(s1@.subrange(0, i as int), '0');
                }
            }
            
            if i < s2.len() {
                let next_idx = if (i + 1) as int <= len2 as int { (i + 1) as int } else { len2 as int };
                assert(s2@.subrange(0, next_idx) == s2@.subrange(0, i as int).push(s2@[i as int]));
                if s2@[i as int] == '1' {
                    lemma_str2int_append_bit(s2@.subrange(0, i as int), '1');
                } else {
                    lemma_str2int_append_bit(s2@.subrange(0, i as int), '0');
                }
            }
        }
        
        result.push(new_bit);
        i = i + 1;
    }
    
    proof {
        assert(s1@.subrange(0, len1 as int) == s1@);
        assert(s2@.subrange(0, len2 as int) == s2@);
        assert(carry == 0);
    }
    
    result
}
// </vc-code>

fn main() {}
}