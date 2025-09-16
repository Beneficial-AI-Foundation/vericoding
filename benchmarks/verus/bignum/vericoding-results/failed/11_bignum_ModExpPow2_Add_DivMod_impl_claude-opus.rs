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
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat }
{
    assert(s.push(c).len() == s.len() + 1);
    assert(s.push(c).subrange(0, s.push(c).len() - 1) == s);
    assert(s.push(c).index(s.push(c).len() - 1) == c);
}

proof fn lemma_exp_int_positive(x: nat, y: nat)
    requires x > 0
    ensures Exp_int(x, y) > 0
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
    } else {
        lemma_exp_int_positive(x, (y - 1) as nat);
        assert(Exp_int(x, (y - 1) as nat) > 0);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

proof fn lemma_exp_int_2_properties(n: nat)
    requires n > 0
    ensures Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat),
            Exp_int(2, n) >= 4 * Exp_int(2, (n - 1) as nat) ==> n >= 2
{
    assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
}

proof fn lemma_exp_int_2_double(n: nat)
    requires n >= 1
    ensures 4 * Exp_int(2, (n - 1) as nat) == 2 * Exp_int(2, n)
{
    lemma_exp_int_2_properties(n);
    assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
    assert(4 * Exp_int(2, (n - 1) as nat) == 2 * 2 * Exp_int(2, (n - 1) as nat));
    assert(2 * 2 * Exp_int(2, (n - 1) as nat) == 2 * Exp_int(2, n));
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
        lemma_exp_int_2_properties(n);
        assert(2 * Exp_int(2, (n - 1) as nat) + 2 <= 2 * Exp_int(2, (n - 1) as nat) + 2 * Exp_int(2, (n - 1) as nat));
        assert(2 * Exp_int(2, (n - 1) as nat) + 2 * Exp_int(2, (n - 1) as nat) == 4 * Exp_int(2, (n - 1) as nat));
        if n >= 2 {
            lemma_exp_int_2_double(n);
            assert(4 * Exp_int(2, (n - 1) as nat) == 2 * Exp_int(2, n));
            assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
            assert(4 * Exp_int(2, (n - 1) as nat) == Exp_int(2, n + 1));
        } else {
            assert(n == 1);
            assert(Exp_int(2, 1) == 2);
            assert(Exp_int(2, 0) == 1);
            assert(4 * Exp_int(2, 0) == 4);
            assert(4 > 2);
        }
        assert(Str2Int(s) < Exp_int(2, n));
    }
}

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
    assert forall |i: int| 0 <= i < s.subrange(start, end).len() implies 
        s.subrange(start, end).index(i) == s.index(start + i) &&
        (s.index(start + i) == '0' || s.index(start + i) == '1') by {
    }
}

proof fn lemma_str2int_reverse_interpretation(s: Seq<char>, i: nat)
    requires ValidBitString(s), i <= s.len()
    ensures Str2Int(s.subrange(0, i as int)) == Str2Int(s.subrange(0, i as int))
{
    // Trivial identity lemma
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
    
    while i < max_len || carry > 0
        invariant
            i <= max_len || (i == max_len && carry <= 1),
            carry <= 1,
            ValidBitString(result@),
            result@.len() == i,
            ({
                let s1_part = if i <= s1@.len() {
                    ValidBitString(s1@.subrange(0, i as int)) &&
                    Str2Int(s1@.subrange(0, i as int))
                } else {
                    Str2Int(s1@)
                };
                let s2_part = if i <= s2@.len() {
                    ValidBitString(s2@.subrange(0, i as int)) &&
                    Str2Int(s2@.subrange(0, i as int))
                } else {
                    Str2Int(s2@)
                };
                Str2Int(result@) + carry as nat * Exp_int(2, i as nat) == s1_part + s2_part
            }),
        decreases max_len + 1 - i + carry as usize
    {
        proof {
            if i < s1@.len() {
                lemma_valid_bit_string_subrange(s1@, 0, (i + 1) as int);
            }
            if i < s2@.len() {
                lemma_valid_bit_string_subrange(s2@, 0, (i + 1) as int);
            }
        }

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
        let old_carry = carry;
        carry = sum >> 1;
        
        proof {
            assert(sum <= 3);
            assert(carry == sum / 2);
            assert((sum & 1) == sum % 2);
        }
        
        result.push(new_bit);
        
        proof {
            let old_result = result@.subrange(0, result@.len() - 1);
            assert(result@ == old_result.push(new_bit));
            lemma_str2int_append(old_result, new_bit);
            
            let old_s1_part = if i <= s1@.len() {
                if i > 0 {
                    lemma_valid_bit_string_subrange(s1@, 0, i as int);
                }
                Str2Int(s1@.subrange(0, i as int))
            } else {
                Str2Int(s1@)
            };
            
            let old_s2_part = if i <= s2@.len() {
                if i > 0 {
                    lemma_valid_bit_string_subrange(s2@, 0, i as int);
                }
                Str2Int(s2@.subrange(0, i as int))
            } else {
                Str2Int(s2@)
            };
            
            let new_s1_part = if i + 1 <= s1@.len() {
                lemma_valid_bit_string_subrange(s1@, 0, (i + 1) as int);
                Str2Int(s1@.subrange(0, (i + 1) as int))
            } else {
                Str2Int(s1@)
            };
            
            let new_s2_part = if i + 1 <= s2@.len() {
                lemma_valid_bit_string_subrange(s2@, 0, (i + 1) as int);
                Str2Int(s2@.subrange(0, (i + 1) as int))
            } else {
                Str2Int(s2@)
            };
            
            if i < s1@.len() {
                lemma_valid_bit_string_subrange(s1@, 0, i as int);
                lemma_valid_bit_string_subrange(s1@, 0, (i + 1) as int);
                let s1_i = s1@.subrange(0, i as int);
                let s1_i1 = s1@.subrange(0, (i + 1) as int);
                assert(s1_i1 == s1_i.push(s1@[i as int]));
                lemma_str2int_append(s1_i, s1@[i as int]);
                assert(new_s1_part == 2 * old_s1_part + if s1@[i as int] == '1' { 1nat } else { 0nat });
            } else {
                assert(new_s1_part == old_s1_part);
            }
            
            if i < s2@.len() {
                lemma_valid_bit_string_subrange(s2@, 0, i as int);
                lemma_valid_bit_string_subrange(s2@, 0, (i + 1) as int);
                let s2_i = s2@.subrange(0, i as int);
                let s2_i1 = s2@.subrange(0, (i + 1) as int);
                assert(s2_i1 == s2_i.push(s2@[i as int]));
                lemma_str2int_append(s2_i, s2@[i as int]);
                assert(new_s2_part == 2 * old_s2_part + if s2@[i as int] == '1' { 1nat } else { 0nat });
            } else {
                assert(new_s2_part == old_s2_part);
            }
            
            let bit1_val = if i < s1@.len() && s1@[i as int] == '1' { 1nat } else { 0nat };
            let bit2_val = if i < s2@.len() && s2@[i as int] == '1' { 1nat } else { 0nat };
            let old_carry_val = old_carry as nat;
            let new_carry_val = carry as nat;
            let new_bit_val = if new_bit == '1' { 1nat } else { 0nat };
            
            assert(bit1 as nat == bit1_val);
            assert(bit2 as nat == bit2_val);
            assert(sum as nat == bit1_val + bit2_val + old_carry_val);
            
            assert((sum & 1) == sum % 2);
            assert(carry == sum / 2);
            assert(new_bit_val == sum as nat % 2);
            assert(new_carry_val == sum as nat / 2);
            assert(sum as nat == new_carry_val * 2 + new_bit_val);
            
            assert(Str2Int(result@) == 2 * Str2Int(old_result) + new_bit_val);
            
            lemma_exp_int_2_properties((i + 1) as nat);
            assert(Exp_int(2, (i + 1) as nat) == 2 * Exp_int(2, i as nat));
            
            assert(Str2Int(result@) + new_carry_val * Exp_int(2, (i + 1) as nat) ==
                   new_s1_part + new_s2_part);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(carry == 0);
        assert(Str2Int(result@) + 0 * Exp_int(2, i as nat) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}