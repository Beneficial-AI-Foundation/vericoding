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
spec fn spec_min(a: int, b: int) -> int {
    if a < b { a } else { b }
}

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
    requires x > 0
    ensures Exp_int(x, y) > 0
    decreases y
{
    reveal_with_fuel(Exp_int, 1);
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
    } else {
        lemma_exp_int_positive(x, (y - 1) as nat);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

proof fn lemma_exp_int_positive_2(y: nat)
    ensures Exp_int(2, y) > 0
    decreases y
{
    lemma_exp_int_positive(2, y);
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

proof fn lemma_subrange_valid_bitstring(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len() as int
    ensures ValidBitString(s.subrange(start, end))
{
    let sub = s.subrange(start, end);
    assert forall |i: int| 0 <= i && i < sub.len() as int implies
        #[trigger] sub.index(i) == '0' || sub.index(i) == '1' by {
        assert(sub.index(i) == s.index(start + i));
    }
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
    reveal_with_fuel(Str2Int, 1);
}

proof fn lemma_subrange_full(s: Seq<char>, i: int)
    requires i >= s.len() as int
    ensures s.subrange(0, spec_min(i, s.len() as int)) == s
{
    assert(spec_min(i, s.len() as int) == s.len() as int);
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
    
    proof {
        lemma_str2int_empty();
        assert(ValidBitString(Seq::<char>::empty()));
    }
    
    while i < max_len || carry > 0
        invariant
            carry <= 1,
            ValidBitString(result@),
            i <= if s1.len() > s2.len() { s1.len() + 1 } else { s2.len() + 1 },
            ValidBitString(s1@.subrange(0, spec_min(i as int, s1@.len() as int))),
            ValidBitString(s2@.subrange(0, spec_min(i as int, s2@.len() as int))),
            i <= s1.len() ==> Str2Int(result@) + (carry as nat) * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, spec_min(i as int, s2@.len() as int))),
            i > s1.len() && i <= s2.len() ==> Str2Int(result@) + (carry as nat) * Exp_int(2, i as nat) == 
                Str2Int(s1@) + Str2Int(s2@.subrange(0, i as int)),
            i > s2.len() && i <= s1.len() ==> Str2Int(result@) + (carry as nat) * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@),
            i > s1.len() && i > s2.len() ==> Str2Int(result@) + (carry as nat) * Exp_int(2, i as nat) == 
                Str2Int(s1@) + Str2Int(s2@),
        decreases
            if i < max_len { (max_len - i) + 2 } else { carry as int }
    {
        let old_carry = carry;
        
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
            
            let s1_curr = if i <= s1.len() { s1@.subrange(0, i as int) } else { s1@ };
            let s2_curr = if i <= s2.len() { s2@.subrange(0, i as int) } else { s2@ };
            let s1_next = if i + 1 <= s1.len() { s1@.subrange(0, (i + 1) as int) } else { s1@ };
            let s2_next = if i + 1 <= s2.len() { s2@.subrange(0, (i + 1) as int) } else { s2@ };
            
            if i < s1.len() {
                assert(s1_next == s1_curr.push(s1@[i as int]));
                lemma_subrange_valid_bitstring(s1@, 0, i as int);
                assert(ValidBitString(s1_curr));
                lemma_str2int_append_bit(s1_curr, s1@[i as int]);
            } else {
                assert(s1_next == s1_curr);
                assert(s1_curr == s1@);
            }
            
            if i < s2.len() {
                assert(s2_next == s2_curr.push(s2@[i as int]));
                lemma_subrange_valid_bitstring(s2@, 0, i as int);
                assert(ValidBitString(s2_curr));
                lemma_str2int_append_bit(s2_curr, s2@[i as int]);
            } else {
                assert(s2_next == s2_curr);
                assert(s2_curr == s2@);
            }
            
            // Maintain ValidBitString invariants for next iteration
            lemma_subrange_valid_bitstring(s1@, 0, spec_min((i + 1) as int, s1@.len() as int));
            lemma_subrange_valid_bitstring(s2@, 0, spec_min((i + 1) as int, s2@.len() as int));
            
            reveal_with_fuel(Exp_int, 1);
            assert(Exp_int(2, (i + 1) as nat) == 2 * Exp_int(2, i as nat));
            
            // Prove bit operations
            assert(bit1 <= 1);
            assert(bit2 <= 1);
            assert(old_carry <= 1);
            assert(sum <= 3); // max is 1 + 1 + 1
            
            if sum == 0 {
                assert(0u8 & 1 == 0);
                assert(0u8 >> 1 == 0);
            } else if sum == 1 {
                assert(1u8 & 1 == 1);
                assert(1u8 >> 1 == 0);
            } else if sum == 2 {
                assert(2u8 & 1 == 0);
                assert(2u8 >> 1 == 1);
            } else if sum == 3 {
                assert(3u8 & 1 == 1);
                assert(3u8 >> 1 == 1);
            }
            
            assert((sum & 1) == (sum % 2));
            assert((sum >> 1) == (sum / 2));
            
            assert(new_bit == (if (sum % 2) == 1 { '1' } else { '0' }));
            assert((carry as nat) == (sum / 2) as nat);
            
            let bit1_val = if i < s1.len() && s1@[i as int] == '1' { 1nat } else { 0nat };
            let bit2_val = if i < s2.len() && s2@[i as int] == '1' { 1nat } else { 0nat };
            
            assert(bit1 as nat == bit1_val);
            assert(bit2 as nat == bit2_val);
            assert(sum as nat == bit1_val + bit2_val + old_carry as nat);
            assert((if new_bit == '1' { 1nat } else { 0nat }) == (sum as nat) % 2);
            
            if i < s1.len() {
                assert(Str2Int(s1_next) == Str2Int(s1_curr) + bit1_val * Exp_int(2, i as nat));
            } else {
                assert(Str2Int(s1_next) == Str2Int(s1_curr));
            }
            
            if i < s2.len() {
                assert(Str2Int(s2_next) == Str2Int(s2_curr) + bit2_val * Exp_int(2, i as nat));
            } else {
                assert(Str2Int(s2_next) == Str2Int(s2_curr));
            }
            
            // Prove termination
            if i >= max_len {
                assert(bit1 == 0);
                assert(bit2 == 0);
                assert(sum == old_carry);
                assert(carry == sum >> 1);
                assert(carry < 2);
                if old_carry == 1 {
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
        if i > s1.len() && i > s2.len() {
            assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
        } else if i > s1.len() {
            assert(s2@.subrange(0, i as int) == s2@);
            assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
        } else if i > s2.len() {
            assert(s1@.subrange(0, i as int) == s1@);
            assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
        } else {
            assert(s1@.subrange(0, i as int) == s1@);
            assert(s2@.subrange(0, spec_min(i as int, s2@.len() as int)) == s2@);
            assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}