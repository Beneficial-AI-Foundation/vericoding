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
// Helper lemmas for Str2Int properties
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
    decreases s.len()
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() - 1) == s);
    assert(s_new.index(s_new.len() - 1) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() - 1) == s);
    assert(s_new.index(s_new.len() - 1) == '1');
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
    assert forall |i: int| 0 <= i && i < s.push(c).len() implies 
        #[trigger] s.push(c).index(i) == '0' || s.push(c).index(i) == '1' by {
        if i < s.len() {
            assert(s.push(c).index(i) == s.index(i));
        } else {
            assert(i == s.len());
            assert(s.push(c).index(i) == c);
        }
    }
}

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
    assert forall |i: int| 0 <= i && i < s.subrange(start, end).len() implies
        #[trigger] s.subrange(start, end).index(i) == '0' || s.subrange(start, end).index(i) == '1' by {
        assert(s.subrange(start, end).index(i) == s.index(start + i));
    }
}

proof fn lemma_str2int_extend(s: Seq<char>, n: int)
    requires ValidBitString(s), 0 <= n <= s.len()
    ensures 
        n == s.len() ==> Str2Int(s.subrange(0, n)) == Str2Int(s),
        n < s.len() && s.index(n) == '0' ==> 
            Str2Int(s.subrange(0, n + 1)) == 2 * Str2Int(s.subrange(0, n)),
        n < s.len() && s.index(n) == '1' ==> 
            Str2Int(s.subrange(0, n + 1)) == 2 * Str2Int(s.subrange(0, n)) + 1
    decreases s.len() - n
{
    if n == s.len() {
        assert(s.subrange(0, n) == s);
    } else {
        let sub = s.subrange(0, n + 1);
        let sub_prefix = s.subrange(0, n);
        assert(sub.len() == n + 1);
        assert(sub.subrange(0, sub.len() - 1) == sub_prefix);
        assert(sub.index(sub.len() - 1) == s.index(n));
    }
}

proof fn lemma_exp_int_properties(x: nat, y: nat)
    ensures 
        y == 0 ==> Exp_int(x, y) == 1,
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
    decreases y
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
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant 
            carry <= 1,
            ValidBitString(result@),
            result@.len() == i,
            {
                let s1_val = if i <= s1@.len() { Str2Int(s1@.subrange(0, i as int)) } else { Str2Int(s1@) };
                let s2_val = if i <= s2@.len() { Str2Int(s2@.subrange(0, i as int)) } else { Str2Int(s2@) };
                Str2Int(result@) + carry as nat * Exp_int(2, i as nat) == s1_val + s2_val
            }
    {
        let mut bit_sum = carry;
        
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
        
        bit_sum = bit_sum + bit1 + bit2;
        
        let result_bit = if bit_sum % 2 == 0 { '0' } else { '1' };
        let new_carry = bit_sum / 2;
        
        proof {
            let old_result = result@;
            lemma_valid_bit_string_push(old_result, result_bit);
            
            if i < s1@.len() {
                lemma_valid_bit_string_subrange(s1@, 0, i as int);
                lemma_valid_bit_string_subrange(s1@, 0, (i + 1) as int);
                lemma_str2int_extend(s1@, i as int);
            }
            
            if i < s2@.len() {
                lemma_valid_bit_string_subrange(s2@, 0, i as int);
                lemma_valid_bit_string_subrange(s2@, 0, (i + 1) as int);
                lemma_str2int_extend(s2@, i as int);
            }
            
            if result_bit == '0' {
                lemma_str2int_append_zero(old_result);
                assert(Str2Int(result@.subrange(0, (i + 1) as int)) == 2 * Str2Int(old_result));
            } else {
                lemma_str2int_append_one(old_result);
                assert(Str2Int(result@.subrange(0, (i + 1) as int)) == 2 * Str2Int(old_result) + 1);
            }
            
            lemma_exp_int_properties(2, i as nat);
            lemma_exp_int_properties(2, (i + 1) as nat);
            assert(Exp_int(2, (i + 1) as nat) == 2 * Exp_int(2, i as nat));
        }
        
        result.push(result_bit);
        carry = new_carry;
        i = i + 1;
    }
    
    proof {
        assert(carry == 0);
        assert(i >= s1@.len() && i >= s2@.len());
        assert(s1@.subrange(0, s1@.len() as int) == s1@);
        assert(s2@.subrange(0, s2@.len() as int) == s2@);
        assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}