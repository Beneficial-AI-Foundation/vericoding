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
/* helper modified by LLM (iteration 6): Fixed seq! macro syntax errors */
proof fn lemma_str2int_zero(s: Seq<char>)
    requires
        ValidBitString(s),
        forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0',
    ensures
        Str2Int(s) == 0,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_zero(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires
        ValidBitString(s),
        bit == '0' || bit == '1',
    ensures
        ValidBitString(s.push(bit)),
        Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat }),
{
    let s_new = s.push(bit);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
}

spec fn seq_repeat_zero(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        seq_repeat_zero((n - 1) as nat).push('0')
    }
}

proof fn lemma_seq_repeat_zero_valid(n: nat)
    ensures ValidBitString(seq_repeat_zero(n))
    decreases n
{
    if n == 0 {
        assert(ValidBitString(Seq::<char>::empty()));
    } else {
        lemma_seq_repeat_zero_valid((n - 1) as nat);
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1nat
    } else {
        2 * pow2((n - 1) as nat)
    }
}

proof fn lemma_pow2_unfold(n: nat)
    requires n > 0,
    ensures pow2(n) == 2 * pow2((n - 1) as nat),
{
}

proof fn lemma_concat_valid(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2),
    ensures ValidBitString(s1 + s2)
{
    assert forall |i: int| 0 <= i && i < (s1 + s2).len() as int implies
        ((s1 + s2).index(i) == '0' || (s1 + s2).index(i) == '1') by {
        if i < s1.len() as int {
            assert((s1 + s2).index(i) == s1.index(i));
        } else {
            assert((s1 + s2).index(i) == s2.index(i - s1.len() as int));
        }
    }
}

proof fn lemma_mul_by_power_of_2(s: Seq<char>, k: nat)
    requires
        ValidBitString(s),
    ensures
        ValidBitString(s + seq_repeat_zero(k)),
        Str2Int(s + seq_repeat_zero(k)) == pow2(k) * Str2Int(s),
    decreases k
{
    lemma_seq_repeat_zero_valid(k);
    lemma_concat_valid(s, seq_repeat_zero(k));
    
    if k == 0 {
        assert(s + seq_repeat_zero(0) == s);
    } else {
        let zeros = seq_repeat_zero(k);
        let prev_zeros = seq_repeat_zero((k - 1) as nat);
        assert(zeros == prev_zeros.push('0'));
        
        lemma_mul_by_power_of_2(s, (k - 1) as nat);
        let combined = s + prev_zeros;
        assert(s + zeros == combined.push('0'));
        lemma_str2int_append_bit(combined, '0');
        assert(Str2Int(s + zeros) == 2 * Str2Int(s + prev_zeros));
        lemma_pow2_unfold(k);
        assert(pow2(k) * Str2Int(s) == 2 * pow2((k - 1) as nat) * Str2Int(s));
    }
}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(Seq::<char>::empty()) == 0);
}

proof fn lemma_multiply_by_zero(s: Seq<char>)
    requires ValidBitString(s),
    ensures 0 * Str2Int(s) == 0,
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
    /* code modified by LLM (iteration 6): Simplified approach with proper invariants */
    if s2.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            lemma_str2int_single_zero();
            assert(Str2Int(result@) == 0);
            assert(Str2Int(s2@) == 0);
            lemma_multiply_by_zero(s1@);
        }
        return result;
    }
    
    if s1.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            lemma_str2int_single_zero();
            assert(Str2Int(result@) == 0);
            assert(Str2Int(s1@) == 0);
            lemma_multiply_by_zero(s2@);
        }
        return result;
    }
    
    // Simple implementation: convert to integers, multiply, convert back
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i: usize = 0;
    while i < s2.len()
        invariant
            0 <= i <= s2.len(),
            ValidBitString(result@),
            result@.len() >= 1,
        decreases s2.len() - i
    {
        if s2[s2.len() - 1 - i] == '1' {
            // Create s1 shifted left by i positions (multiply by 2^i)
            let mut shifted = Vec::<char>::new();
            let mut j: usize = 0;
            while j < s1.len()
                invariant
                    0 <= j <= s1.len(),
                    ValidBitString(shifted@),
                    shifted@.len() == j,
                    forall |k: int| 0 <= k && k < j ==> shifted@.index(k) == s1@.index(k),
                decreases s1.len() - j
            {
                shifted.push(s1[j]);
                j = j + 1;
            }
            
            // Add i zeros at the end
            let mut k: usize = 0;
            while k < i
                invariant
                    0 <= k <= i,
                    ValidBitString(shifted@),
                    shifted@.len() == s1.len() + k,
                decreases i - k
            {
                shifted.push('0');
                k = k + 1;
            }
            
            proof {
                lemma_mul_by_power_of_2(s1@, i as nat);
                assert(ValidBitString(shifted@));
            }
            
            // Add shifted to result
            let old_result = result;
            result = add_binary_helper(&old_result, &shifted);
        }
        i = i + 1;
    }
    
    result
}

exec fn add_binary_helper(s1: &Vec<char>, s2: &Vec<char>) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        ValidBitString(res@),
{
    // Simple implementation that just ensures valid bit string
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            0 <= i,
            ValidBitString(result@),
            carry <= 1,
        decreases if i < max_len { max_len - i + 1 } else { carry as int }
    {
        let mut sum = carry;
        if i < s1.len() {
            sum = sum + if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 };
        }
        if i < s2.len() {
            sum = sum + if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 };
        }
        
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i = i + 1;
        
        if i > max_len && carry == 0 {
            break;
        }
    }
    
    // Reverse the result
    let mut reversed = Vec::<char>::new();
    if result.len() == 0 {
        reversed.push('0');
    } else {
        let mut j: usize = 0;
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                ValidBitString(reversed@),
                reversed@.len() == j,
            decreases result.len() - j
        {
            reversed.push(result[result.len() - 1 - j]);
            j = j + 1;
        }
    }
    
    reversed
}
// </vc-code>

fn main() {}
}
