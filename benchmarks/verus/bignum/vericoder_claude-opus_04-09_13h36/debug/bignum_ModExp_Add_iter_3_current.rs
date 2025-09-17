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
    if s.len() == 0 {
        assert(s.push('0').len() == 1);
        assert(Str2Int(s.push('0')) == 0);
    } else {
        assert(s.push('0').subrange(0, s.push('0').len() - 1) == s);
    }
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push('1').len() == 1);
        assert(Str2Int(s.push('1')) == 1);
    } else {
        assert(s.push('1').subrange(0, s.push('1').len() - 1) == s);
    }
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

proof fn lemma_str2int_reverse_helper(s: Seq<char>, acc: Seq<char>, idx: int)
    requires 
        ValidBitString(s),
        ValidBitString(acc),
        0 <= idx <= s.len(),
        acc.len() == idx,
        forall |k: int| 0 <= k && k < idx ==> #[trigger] acc[k] == s[s.len() - 1 - k]
    ensures 
        idx == s.len() ==> Str2Int(acc) == Str2Int(s)
    decreases s.len() - idx
{
    if idx == s.len() {
        // Base case: prove Str2Int(acc) == Str2Int(s)
        // This requires showing that the reversed representation has the same value
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
    let n1 = s1.len();
    let n2 = s2.len();
    
    while i < n1 || i < n2 || carry > 0
        invariant 
            i <= n1,
            i <= n2,
            carry <= 1,
            ValidBitString(result@),
            Str2Int(result@) + carry as nat * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int))
    {
        let mut bit_sum = carry;
        
        if i < n1 {
            let c1 = s1[n1 - 1 - i];
            if c1 == '1' {
                bit_sum = bit_sum + 1;
            }
        }
        
        if i < n2 {
            let c2 = s2[n2 - 1 - i];
            if c2 == '1' {
                bit_sum = bit_sum + 1;
            }
        }
        
        let result_bit = if bit_sum % 2 == 0 { '0' } else { '1' };
        carry = bit_sum / 2;
        
        proof {
            let old_result = result@;
            lemma_valid_bit_string_push(old_result, result_bit);
            
            if result_bit == '0' {
                lemma_str2int_append_zero(old_result);
            } else {
                lemma_str2int_append_one(old_result);
            }
            
            // Update s1 contribution
            if i < n1 {
                let s1_sub_old = s1@.subrange(0, i as int);
                let s1_sub_new = s1@.subrange(0, (i + 1) as int);
                assert(s1_sub_new == s1_sub_old.push(s1@[n1 - 1 - i]));
                
                if s1@[n1 - 1 - i] == '0' {
                    lemma_str2int_append_zero(s1_sub_old);
                } else {
                    lemma_str2int_append_one(s1_sub_old);
                }
            }
            
            // Update s2 contribution
            if i < n2 {
                let s2_sub_old = s2@.subrange(0, i as int);
                let s2_sub_new = s2@.subrange(0, (i + 1) as int);
                assert(s2_sub_new == s2_sub_old.push(s2@[n2 - 1 - i]));
                
                if s2@[n2 - 1 - i] == '0' {
                    lemma_str2int_append_zero(s2_sub_old);
                } else {
                    lemma_str2int_append_one(s2_sub_old);
                }
            }
        }
        
        result.push(result_bit);
        i = i + 1;
    }
    
    // Reverse the result to get proper bit order
    let mut final_result = Vec::<char>::new();
    let mut j: usize = 0;
    
    while j < result.len()
        invariant
            j <= result.len(),
            final_result@.len() == j,
            ValidBitString(final_result@),
            forall |k: int| 0 <= k && k < j as int ==> 
                #[trigger] final_result@[k] == result@[result@.len() - 1 - k]
    {
        let idx = result.len() - 1 - j;
        let c = result[idx];
        proof {
            lemma_valid_bit_string_push(final_result@, c);
        }
        final_result.push(c);
        j = j + 1;
    }
    
    proof {
        assert(final_result@.len() == result@.len());
        assert(i >= n1 && i >= n2);
        assert(s1@.subrange(0, n1 as int) == s1@);
        assert(s2@.subrange(0, n2 as int) == s2@);
        assert(carry == 0);
        assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
        
        // The reversing preserves the sum since we built result in reverse order
        lemma_str2int_reverse_helper(result@, final_result@, j as int);
    }
    
    return final_result;
}
// </vc-code>

fn main() {}
}