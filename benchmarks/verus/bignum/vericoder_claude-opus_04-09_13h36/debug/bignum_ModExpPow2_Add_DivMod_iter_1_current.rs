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
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1 } else { 0 }
{
    assert(s.push(c).len() == s.len() + 1);
    assert(s.push(c).subrange(0, s.push(c).len() - 1) == s);
    assert(s.push(c).index(s.push(c).len() - 1) == c);
}

proof fn lemma_exp_int_positive(x: nat, y: nat)
    ensures Exp_int(x, y) > 0
    decreases y
{
    if y == 0 {
    } else {
        lemma_exp_int_positive(x, (y - 1) as nat);
    }
}

proof fn lemma_str2int_bounded(s: Seq<char>, n: nat)
    requires ValidBitString(s), s.len() == n
    ensures Str2Int(s) < Exp_int(2, n)
    decreases n
{
    if n == 0 {
        assert(s.len() == 0);
    } else {
        let s_prefix = s.subrange(0, s.len() - 1);
        assert(ValidBitString(s_prefix));
        assert(s_prefix.len() == n - 1);
        lemma_str2int_bounded(s_prefix, (n - 1) as nat);
        let last_bit = if s.index(s.len() - 1) == '1' { 1nat } else { 0nat };
        assert(last_bit <= 1);
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + last_bit);
        assert(Str2Int(s_prefix) < Exp_int(2, (n - 1) as nat));
        assert(Str2Int(s) < 2 * Exp_int(2, (n - 1) as nat) + 2);
        assert(2 * Exp_int(2, (n - 1) as nat) + 2 <= Exp_int(2, n));
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
    let mut result: Vec<char> = Vec::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    assert forall |j: int| 0 <= j && j < result@.len() ==> result@.index(j) == '0' || result@.index(j) == '1' by {}
    assert(ValidBitString(result@));
    
    while i < max_len || carry > 0
        invariant
            i <= max_len,
            carry <= 1,
            ValidBitString(result@),
            result@.len() == i,
            Str2Int(result@) + carry * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int)),
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
        let new_bit = if (sum & 1) == 1 { '1' } else { '0' };
        carry = sum >> 1;
        
        result.push(new_bit);
        
        proof {
            let old_result = result@.subrange(0, result@.len() - 1);
            assert(old_result.len() == i);
            assert(result@ == old_result.push(new_bit));
            lemma_str2int_append(old_result, new_bit);
            
            let s1_next = s1@.subrange(0, (i + 1) as int);
            let s2_next = s2@.subrange(0, (i + 1) as int);
            
            if i < s1@.len() {
                assert(s1_next == s1@.subrange(0, i as int).push(s1@.index(i as int)));
                lemma_str2int_append(s1@.subrange(0, i as int), s1@.index(i as int));
            } else {
                assert(s1_next == s1@.subrange(0, i as int));
            }
            
            if i < s2@.len() {
                assert(s2_next == s2@.subrange(0, i as int).push(s2@.index(i as int)));
                lemma_str2int_append(s2@.subrange(0, i as int), s2@.index(i as int));
            } else {
                assert(s2_next == s2@.subrange(0, i as int));
            }
            
            let bit1_val = if i < s1@.len() && s1@.index(i as int) == '1' { 1nat } else { 0nat };
            let bit2_val = if i < s2@.len() && s2@.index(i as int) == '1' { 1nat } else { 0nat };
            let old_carry_val = carry as nat;
            
            assert(bit1 as nat == bit1_val);
            assert(bit2 as nat == bit2_val);
            assert(sum as nat == bit1_val + bit2_val + old_carry_val);
            
            let new_bit_val = if new_bit == '1' { 1nat } else { 0nat };
            assert(new_bit_val == (sum & 1) as nat);
            assert(carry as nat == (sum >> 1) as nat);
            
            assert(Str2Int(result@) == 2 * Str2Int(old_result) + new_bit_val);
            assert(Str2Int(s1_next) == 2 * Str2Int(s1@.subrange(0, i as int)) + bit1_val);
            assert(Str2Int(s2_next) == 2 * Str2Int(s2@.subrange(0, i as int)) + bit2_val);
            
            assert(sum as nat == bit1_val + bit2_val + old_carry_val);
            assert(new_bit_val + 2 * (carry as nat) == sum as nat);
            
            assert(Str2Int(result@) + carry * Exp_int(2, (i + 1) as nat) ==
                   Str2Int(s1_next) + Str2Int(s2_next));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s1@.subrange(0, s1@.len() as int) == s1@);
        assert(s2@.subrange(0, s2@.len() as int) == s2@);
        assert(carry == 0);
        assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}