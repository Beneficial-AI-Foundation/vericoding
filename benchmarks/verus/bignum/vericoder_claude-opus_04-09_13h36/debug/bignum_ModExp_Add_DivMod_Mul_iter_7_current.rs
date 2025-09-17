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
    ensures Str2Int(s.push(bit)) == 2 * Str2Int(s) + if bit == '1' { 1nat } else { 0nat }
    decreases s.len()
{
    reveal(Str2Int);
    let s_new = s.push(bit);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
    assert(s_new.index(s_new.len() as int - 1) == bit);
}

proof fn lemma_str2int_empty()
    ensures Str2Int(seq![]) == 0
{
    reveal(Str2Int);
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
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

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, i: int, j: int)
    requires ValidBitString(s), 0 <= i <= j <= s.len() as int
    ensures ValidBitString(s.subrange(i, j))
{
    assert forall |k: int| 0 <= k && k < s.subrange(i, j).len() as int implies
        s.subrange(i, j).index(k) == '0' || s.subrange(i, j).index(k) == '1' by {
        assert(s.subrange(i, j).index(k) == s.index(i + k));
    }
}

proof fn lemma_bit_arithmetic(bit1: u8, bit2: u8, carry: u8)
    requires bit1 <= 1, bit2 <= 1, carry <= 1
    ensures 
        bit1 + bit2 + carry <= 3,
        (bit1 as nat + bit2 as nat + carry as nat) % 2 == if (bit1 + bit2 + carry) % 2 == 0 { 0nat } else { 1nat },
        (bit1 as nat + bit2 as nat + carry as nat) / 2 == ((bit1 + bit2 + carry) / 2) as nat
{
    let sum = bit1 + bit2 + carry;
    assert(sum <= 3);
    
    // Prove the modulo relationship
    if sum == 0 {
        assert(sum % 2 == 0);
        assert(0nat % 2 == 0);
    } else if sum == 1 {
        assert(sum % 2 == 1);
        assert(1nat % 2 == 1);
    } else if sum == 2 {
        assert(sum % 2 == 0);
        assert(2nat % 2 == 0);
    } else {
        assert(sum == 3);
        assert(sum % 2 == 1);
        assert(3nat % 2 == 1);
    }
    
    // Prove the division relationship
    if sum == 0 || sum == 1 {
        assert(sum / 2 == 0);
        assert((sum as nat) / 2 == 0);
    } else {
        assert(sum == 2 || sum == 3);
        assert(sum / 2 == 1);
        assert((sum as nat) / 2 == 1);
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
    
    let max_len = if s1.len() >= s2.len() { s1.len() } else { s2.len() };
    
    proof {
        lemma_valid_bit_string_subrange(s1@, 0, 0);
        lemma_valid_bit_string_subrange(s2@, 0, 0);
        lemma_str2int_empty();
    }
    
    while i < s1.len() || i < s2.len() || carry != 0
        invariant 
            i <= s1.len(),
            i <= s2.len(),
            i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            ValidBitString(s1@.subrange(0, i as int)),
            ValidBitString(s2@.subrange(0, i as int)),
            Str2Int(result@) == Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int)) + carry as nat,
            i >= max_len ==> (i == max_len || (i == max_len + 1 && carry == 0)),
        decreases max_len + 2 - i
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
        
        let old_carry = carry;
        let sum: u8 = bit1 + bit2 + carry;
        let new_bit = if (sum & 1) == 1 { '1' } else { '0' };
        carry = sum >> 1;
        
        proof {
            lemma_bit_arithmetic(bit1, bit2, old_carry);
            assert((sum & 1) == (sum % 2));
            assert((sum >> 1) == (sum / 2));
            assert((sum % 2) as nat == (bit1 as nat + bit2 as nat + old_carry as nat) % 2);
            assert((sum / 2) as nat == (bit1 as nat + bit2 as nat + old_carry as nat) / 2);
            
            let old_s1_range = s1@.subrange(0, i as int);
            let old_s2_range = s2@.subrange(0, i as int);
            
            if i < s1.len() {
                lemma_valid_bit_string_subrange(s1@, 0, (i + 1) as int);
                assert(s1@.subrange(0, (i + 1) as int).subrange(0, i as int) =~= old_s1_range);
                assert(s1@.subrange(0, (i + 1) as int).index(i as int) == s1@[i as int]);
                lemma_str2int_append_bit(old_s1_range, s1@[i as int]);
                assert(Str2Int(s1@.subrange(0, (i + 1) as int)) == 
                       2 * Str2Int(old_s1_range) + bit1 as nat);
            }
            
            if i < s2.len() {
                lemma_valid_bit_string_subrange(s2@, 0, (i + 1) as int);
                assert(s2@.subrange(0, (i + 1) as int).subrange(0, i as int) =~= old_s2_range);
                assert(s2@.subrange(0, (i + 1) as int).index(i as int) == s2@[i as int]);
                lemma_str2int_append_bit(old_s2_range, s2@[i as int]);
                assert(Str2Int(s2@.subrange(0, (i + 1) as int)) == 
                       2 * Str2Int(old_s2_range) + bit2 as nat);
            }
            
            lemma_valid_bit_string_push(result@, new_bit);
            lemma_str2int_append_bit(result@, new_bit);
            
            let next_s1_val = if i < s1.len() { 
                Str2Int(s1@.subrange(0, (i + 1) as int)) 
            } else { 
                Str2Int(s1@.subrange(0, i as int)) 
            };
            
            let next_s2_val = if i < s2.len() { 
                Str2Int(s2@.subrange(0, (i + 1) as int)) 
            } else { 
                Str2Int(s2@.subrange(0, i as int)) 
            };
            
            assert(Str2Int(result@.push(new_bit)) == 
                   2 * Str2Int(result@) + (if new_bit == '1' { 1nat } else { 0nat }));
            assert(Str2Int(result@.push(new_bit)) == 
                   2 * (Str2Int(old_s1_range) + Str2Int(old_s2_range) + old_carry as nat) + 
                   (sum % 2) as nat);
            assert(Str2Int(result@.push(new_bit)) == next_s1_val + next_s2_val + carry as nat);
            
            assert(sum <= 3);
            assert((sum / 2) <= 1);
        }
        
        result.push(new_bit);
        i = i + 1;
    }
    
    proof {
        assert(i >= s1.len() && i >= s2.len());
        assert(s1@.subrange(0, s1.len() as int) =~= s1@);
        assert(s2@.subrange(0, s2.len() as int) =~= s2@);
        assert(carry == 0);
        assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}