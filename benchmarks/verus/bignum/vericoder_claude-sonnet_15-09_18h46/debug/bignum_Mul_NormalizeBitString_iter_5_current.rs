use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): added spec helper function for max */
spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
}

proof fn lemma_str2int_distributive(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1) * Str2Int(s2) == Str2Int(s2) * Str2Int(s1)
{
}

proof fn lemma_str2int_zero()
    ensures Str2Int(seq!['0']) == 0
{
}

proof fn lemma_zero_mult(s: Seq<char>)
    requires ValidBitString(s)
    ensures 0 * Str2Int(s) == 0
{
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced .max() with if-else for decreases clause */
    if s1.len() == 0 || s2.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    let mut i = 0;
    
    while i < s2.len()
        invariant
            ValidBitString(result@),
            i <= s2.len(),
        decreases s2.len() - i
    {
        if s2[i] == '1' {
            let mut shift_amount = 0;
            let mut shifted_s1 = Vec::new();
            
            while shift_amount < i
                invariant
                    shift_amount <= i,
                    ValidBitString(shifted_s1@),
                decreases i - shift_amount
            {
                shifted_s1.push('0');
                shift_amount += 1;
            }
            
            let mut j = 0;
            while j < s1.len()
                invariant
                    j <= s1.len(),
                    ValidBitString(shifted_s1@),
                decreases s1.len() - j
            {
                shifted_s1.push(s1[j]);
                j += 1;
            }
            
            let mut carry = 0;
            let mut k = 0;
            let mut new_result = Vec::new();
            let max_len = if result.len() >= shifted_s1.len() { result.len() } else { shifted_s1.len() };
            
            while k < max_len || carry > 0
                invariant
                    ValidBitString(new_result@),
                    carry <= 1,
                decreases max_len - k + carry
            {
                let r_bit = if k < result.len() { if result[k] == '1' { 1 } else { 0 } } else { 0 };
                let s_bit = if k < shifted_s1.len() { if shifted_s1[k] == '1' { 1 } else { 0 } } else { 0 };
                
                let sum = r_bit + s_bit + carry;
                new_result.push(if sum % 2 == 1 { '1' } else { '0' });
                carry = sum / 2;
                k += 1;
            }
            
            result = new_result;
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
