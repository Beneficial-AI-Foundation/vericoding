// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed indexing to avoid using int type in executable code */
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1nat } else { 2nat * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_properties()
    ensures
        forall|n: nat| pow2(n + 1) == 2nat * pow2(n),
        pow2(0nat) == 1nat,
{
}

proof fn lemma_str2int_shift(s: Seq<char>)
    requires
        valid_bit_string(s),
    ensures
        str2int(seq!['0'].add(s)) == str2int(s),
        s.len() > 0 ==> str2int(seq!['1'].add(s)) == pow2(s.len() as nat) + str2int(s),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(str2int(seq!['0']) == 0nat);
        assert(str2int(seq!['1']) == 1nat);
        assert(pow2(0nat) == 1nat);
    } else {
        let s1 = s.subrange(0, s.len() - 1);
        let last = s[s.len() - 1];
        lemma_str2int_shift(s1);
        
        assert(seq!['0'].add(s) == seq!['0'].add(s1).push(last));
        assert(seq!['1'].add(s) == seq!['1'].add(s1).push(last));
        
        if last == '1' {
            assert(str2int(seq!['0'].add(s)) == 2nat * str2int(seq!['0'].add(s1)) + 1nat);
            assert(str2int(seq!['1'].add(s)) == 2nat * str2int(seq!['1'].add(s1)) + 1nat);
        } else {
            assert(str2int(seq!['0'].add(s)) == 2nat * str2int(seq!['0'].add(s1)));
            assert(str2int(seq!['1'].add(s)) == 2nat * str2int(seq!['1'].add(s1)));
        }
    }
}

fn add_binary(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires
        valid_bit_string(s1@),
        valid_bit_string(s2@),
    ensures
        valid_bit_string(res@),
        str2int(res@) == str2int(s1@) + str2int(s2@),
{
    let mut result = Vec::new();
    let mut carry = false;
    let mut i = (s1.len() as i32) - 1;
    let mut j = (s2.len() as i32) - 1;
    
    while i >= 0 || j >= 0 || carry
        invariant
            valid_bit_string(result@),
            i >= -1 && i < s1.len() as i32,
            j >= -1 && j < s2.len() as i32,
    {
        let bit1 = if i >= 0 { s1[i as usize] == '1' } else { false };
        let bit2 = if j >= 0 { s2[j as usize] == '1' } else { false };
        
        let sum = (if bit1 { 1u8 } else { 0u8 }) + (if bit2 { 1u8 } else { 0u8 }) + (if carry { 1u8 } else { 0u8 });
        result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum >= 2;
        
        if i >= 0 { i = i - 1; }
        if j >= 0 { j = j - 1; }
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed indexing to use usize without casting to int */
    let norm1 = normalize_bit_string(s1@);
    let norm2 = normalize_bit_string(s2@);
    
    let mut s1_vec = Vec::new();
    let mut s2_vec = Vec::new();
    
    let mut k: usize = 0;
    while k < norm1.len()
        invariant
            0 <= k <= norm1.len(),
            s1_vec@.len() == k,
            forall|m: int| 0 <= m < k ==> s1_vec@[m] == norm1[m],
    {
        proof {
            assert(0 <= k < norm1.len());
        }
        s1_vec.push(norm1[k as int]);
        k = k + 1;
    }
    
    k = 0;
    while k < norm2.len()
        invariant
            0 <= k <= norm2.len(),
            s2_vec@.len() == k,
            forall|m: int| 0 <= m < k ==> s2_vec@[m] == norm2[m],
    {
        proof {
            assert(0 <= k < norm2.len());
        }
        s2_vec.push(norm2[k as int]);
        k = k + 1;
    }
    
    assert(s1_vec@ == norm1);
    assert(s2_vec@ == norm2);
    
    let mut result = Vec::new();
    result.push('0');
    
    let mut i = s2_vec.len();
    while i > 0
        invariant
            0 <= i <= s2_vec.len(),
            valid_bit_string(result@),
            valid_bit_string(s2_vec@),
            valid_bit_string(s1_vec@),
    {
        i = i - 1;
        if s2_vec[i] == '1' {
            let mut shifted = s1_vec.clone();
            let mut shift_count = (s2_vec.len() - 1) - i;
            while shift_count > 0
                invariant
                    valid_bit_string(shifted@),
            {
                shifted.push('0');
                shift_count = shift_count - 1;
            }
            result = add_binary(result, shifted);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}