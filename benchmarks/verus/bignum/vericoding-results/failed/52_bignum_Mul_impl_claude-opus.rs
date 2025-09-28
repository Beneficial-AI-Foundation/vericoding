// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
    0nat 
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type mismatch by casting nat to int */
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires
        valid_bit_string(s)
    ensures
        str2int(s.push('0')) == 2 * str2int(s)
    decreases s.len()
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new[s_new.len() - 1] == '0');
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires
        valid_bit_string(s)
    ensures
        str2int(s.push('1')) == 2 * str2int(s) + 1
    decreases s.len()
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new[s_new.len() - 1] == '1');
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
}

fn add_binary(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires
        valid_bit_string(s1@),
        valid_bit_string(s2@)
    ensures
        valid_bit_string(res@),
        str2int(res@) == str2int(s1@) + str2int(s2@)
{
    let mut result = Vec::new();
    let mut carry = false;
    let mut i: usize = 0;
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    
    while i < max_len || carry
        invariant
            i <= max_len + 1,
            valid_bit_string(result@),
            str2int(result@) + (if carry { pow2(i as nat) } else { 0 }) == 
                str2int(if i <= len1 { s1@.subrange(0, i as int) } else { s1@ }) + 
                str2int(if i <= len2 { s2@.subrange(0, i as int) } else { s2@ })
        decreases (max_len - i) as nat + (if carry { 1nat } else { 0nat })
    {
        let bit1 = if i < len1 { s1[i] == '1' } else { false };
        let bit2 = if i < len2 { s2[i] == '1' } else { false };
        
        let sum = (if bit1 { 1 } else { 0 }) + (if bit2 { 1 } else { 0 }) + (if carry { 1 } else { 0 });
        let new_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum >= 2;
        
        result.push(new_bit);
        i = i + 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}

fn shift_left(s: Vec<char>, n: usize) -> (res: Vec<char>)
    requires
        valid_bit_string(s@),
        n < 1000000
    ensures
        valid_bit_string(res@),
        str2int(res@) == str2int(s@) * pow2(n as nat)
    decreases n
{
    if n == 0 {
        return s;
    }
    
    let mut result = s.clone();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            valid_bit_string(result@),
            result@.len() == s@.len() + i,
            str2int(result@) == str2int(s@) * pow2(i as nat)
        decreases n - i
    {
        proof {
            lemma_str2int_append_zero(result@);
            lemma_pow2_unfold(i as nat);
        }
        result.push('0');
        i = i + 1;
    }
    
    result
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_unfold(n: nat)
    ensures
        pow2(n + 1) == 2 * pow2(n)
{
}

proof fn lemma_str2int_empty()
    ensures str2int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_mul_zero(s: Seq<char>)
    requires valid_bit_string(s)
    ensures str2int(s) * 0 == 0
{
}

proof fn lemma_str2int_subrange_full(s: Seq<char>, i: int)
    requires
        valid_bit_string(s),
        0 <= i,
        i >= s.len()
    ensures
        str2int(s.subrange(0, s.len() as int)) == str2int(s)
{
    assert(s.subrange(0, s.len() as int) =~= s);
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed type mismatch in proof block */
    let mut result = Vec::new();
    result.push('0');
    
    if s1.len() == 0 || s2.len() == 0 {
        proof {
            lemma_str2int_empty();
            lemma_mul_zero(s1@);
            lemma_mul_zero(s2@);
        }
        return result;
    }
    
    let mut i: usize = 0;
    let len2 = s2.len();
    
    proof {
        lemma_str2int_empty();
        assert(s2@.subrange(0, 0) =~= Seq::<char>::empty());
        assert(str2int(s2@.subrange(0, 0)) == 0);
        lemma_mul_zero(s1@);
        assert(str2int(result@) == 0);
        assert(str2int(s1@) * 0 == 0);
        assert(str2int(result@) == str2int(s1@) * str2int(s2@.subrange(0, 0)));
    }
    
    while i < len2
        invariant
            i <= len2,
            i < 1000000,
            valid_bit_string(result@),
            str2int(result@) == str2int(s1@) * str2int(s2@.subrange(0, i as int))
        decreases len2 - i
    {
        if s2[i] == '1' {
            let shifted = shift_left(s1.clone(), i);
            result = add_binary(result, shifted);
        }
        i = i + 1;
    }
    
    proof {
        assert(i == len2);
        assert(s2@.subrange(0, len2 as int) =~= s2@);
        lemma_str2int_subrange_full(s2@, len2 as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}