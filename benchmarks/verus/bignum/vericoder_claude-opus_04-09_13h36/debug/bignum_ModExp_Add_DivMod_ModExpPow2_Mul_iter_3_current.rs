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
    reveal_with_fuel(Str2Int, 1);
    let s_new = s.push(bit);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == bit);
}

proof fn lemma_exp_int_positive(x: nat, y: nat)
    ensures Exp_int(x, y) > 0
    decreases y
{
    reveal_with_fuel(Exp_int, 1);
    if y > 0 {
        lemma_exp_int_positive(x, (y - 1) as nat);
    }
}

proof fn lemma_str2int_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Exp_int(2, s.len() as nat)
    decreases s.len()
{
    reveal_with_fuel(Str2Int, 1);
    reveal_with_fuel(Exp_int, 1);
    if s.len() > 0 {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert(ValidBitString(s_prefix)) by {
            assert forall |i: int| 0 <= i && i < s_prefix.len() as int implies 
                s_prefix.index(i) == '0' || s_prefix.index(i) == '1' by {
                assert(s_prefix.index(i) == s.index(i));
            }
        }
        lemma_str2int_bound(s_prefix);
        let last_bit = if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat };
        assert(last_bit <= 1);
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + last_bit);
        assert(Str2Int(s_prefix) < Exp_int(2, s_prefix.len() as nat));
        assert(s_prefix.len() as nat == (s.len() - 1) as nat);
        assert(Exp_int(2, s.len() as nat) == 2 * Exp_int(2, (s.len() - 1) as nat));
        assert(2 * Str2Int(s_prefix) < 2 * Exp_int(2, (s.len() - 1) as nat));
        assert(Str2Int(s) < 2 * Exp_int(2, (s.len() - 1) as nat));
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
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            carry <= 1,
            ValidBitString(result@),
            i <= max_len + 1,
            Str2Int(result@) + (carry as nat) * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int)),
        decreases
            if i < max_len { (max_len - i) + 2 } else { carry as int }
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
        let new_bit = if sum & 1 == 1 { '1' } else { '0' };
        carry = sum >> 1;
        
        proof {
            let old_result = result@;
            let new_result = old_result.push(new_bit);
            
            lemma_str2int_append_bit(old_result, new_bit);
            assert(Str2Int(new_result) == 2 * Str2Int(old_result) + (if new_bit == '1' { 1nat } else { 0nat }));
            
            let s1_next = s1@.subrange(0, (i + 1) as int);
            let s2_next = s2@.subrange(0, (i + 1) as int);
            let s1_curr = s1@.subrange(0, i as int);
            let s2_curr = s2@.subrange(0, i as int);
            
            if i < s1.len() {
                assert(s1_next == s1_curr.push(s1@[i as int]));
                assert(ValidBitString(s1_curr)) by {
                    assert forall |j: int| 0 <= j && j < s1_curr.len() as int implies
                        s1_curr.index(j) == '0' || s1_curr.index(j) == '1' by {
                        assert(s1_curr.index(j) == s1@.index(j));
                    }
                }
                lemma_str2int_append_bit(s1_curr, s1@[i as int]);
            } else {
                assert(s1_next == s1_curr);
            }
            
            if i < s2.len() {
                assert(s2_next == s2_curr.push(s2@[i as int]));
                assert(ValidBitString(s2_curr)) by {
                    assert forall |j: int| 0 <= j && j < s2_curr.len() as int implies
                        s2_curr.index(j) == '0' || s2_curr.index(j) == '1' by {
                        assert(s2_curr.index(j) == s2@.index(j));
                    }
                }
                lemma_str2int_append_bit(s2_curr, s2@[i as int]);
            } else {
                assert(s2_next == s2_curr);
            }
            
            reveal_with_fuel(Exp_int, 1);
            assert(Exp_int(2, (i + 1) as nat) == 2 * Exp_int(2, i as nat));
            
            assert(sum == bit1 + bit2 + (carry as u8));
            assert((sum & 1) == (sum % 2));
            assert((sum >> 1) == (sum / 2));
            assert(new_bit == (if (sum % 2) == 1 { '1' } else { '0' }));
            assert((carry as nat) == (sum / 2) as nat);
            
            let bit1_val = if i < s1.len() && s1@[i as int] == '1' { 1nat } else { 0nat };
            let bit2_val = if i < s2.len() && s2@[i as int] == '1' { 1nat } else { 0nat };
            
            assert(bit1 as nat == bit1_val);
            assert(bit2 as nat == bit2_val);
            assert(sum as nat == bit1_val + bit2_val + (carry as nat));
            assert((if new_bit == '1' { 1nat } else { 0nat }) == (sum as nat) % 2);
            assert((carry as nat) == (sum as nat) / 2);
            
            assert(Str2Int(s1_next) == Str2Int(s1_curr) + bit1_val * Exp_int(2, i as nat));
            assert(Str2Int(s2_next) == Str2Int(s2_curr) + bit2_val * Exp_int(2, i as nat));
            
            assert(Str2Int(new_result) + (carry as nat) * Exp_int(2, (i + 1) as nat) ==
                   Str2Int(s1_next) + Str2Int(s2_next));
            
            // Prove termination
            if i >= max_len {
                assert(bit1 == 0);
                assert(bit2 == 0);
                assert(sum == carry);
                assert(carry == sum >> 1);
                assert(carry < 2);
                if carry == 1 {
                    assert(sum == 1);
                    assert(sum >> 1 == 0);
                    assert(carry == 0);
                }
            }
        }
        
        result.push(new_bit);
        i = i + 1;
    }
    
    proof {
        assert(i >= max_len);
        assert(carry == 0);
        assert(s1@.subrange(0, i as int) == s1@);
        assert(s2@.subrange(0, i as int) == s2@);
        assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}