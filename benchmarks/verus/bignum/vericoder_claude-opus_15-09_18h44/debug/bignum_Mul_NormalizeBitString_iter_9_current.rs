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
/* helper modified by LLM (iteration 9): Complete multiplication helper functions */
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

proof fn lemma_seq_repeat_zero_is_zeros(n: nat)
    ensures forall |i: int| 0 <= i && i < seq_repeat_zero(n).len() as int ==> seq_repeat_zero(n).index(i) == '0'
    decreases n
{
    if n == 0 {
    } else {
        lemma_seq_repeat_zero_is_zeros((n - 1) as nat);
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

proof fn lemma_str2int_concat_zeros(s: Seq<char>, zeros: Seq<char>)
    requires
        ValidBitString(s),
        ValidBitString(zeros),
        forall |i: int| 0 <= i && i < zeros.len() as int ==> zeros.index(i) == '0',
    ensures
        Str2Int(s + zeros) == pow2(zeros.len() as nat) * Str2Int(s),
    decreases zeros.len()
{
    if zeros.len() == 0 {
        assert(s + zeros == s);
        assert(pow2(0) == 1);
    } else {
        let init = zeros.subrange(0, zeros.len() as int - 1);
        assert(zeros == init.push('0'));
        assert forall |i: int| 0 <= i && i < init.len() as int implies init.index(i) == '0' by {
            assert(init.index(i) == zeros.index(i));
        }
        lemma_str2int_concat_zeros(s, init);
        assert(s + zeros == (s + init).push('0'));
        lemma_concat_valid(s, init);
        lemma_str2int_append_bit(s + init, '0');
        assert(Str2Int(s + zeros) == 2 * Str2Int(s + init));
        assert(Str2Int(s + init) == pow2(init.len() as nat) * Str2Int(s));
        assert(pow2(zeros.len() as nat) == 2 * pow2((zeros.len() - 1) as nat));
    }
}

proof fn lemma_mul_by_power_of_2(s: Seq<char>, k: nat)
    requires
        ValidBitString(s),
    ensures
        ValidBitString(s + seq_repeat_zero(k)),
        Str2Int(s + seq_repeat_zero(k)) == pow2(k) * Str2Int(s),
{
    lemma_seq_repeat_zero_valid(k);
    lemma_concat_valid(s, seq_repeat_zero(k));
    let zeros = seq_repeat_zero(k);
    lemma_seq_repeat_zero_is_zeros(k);
    lemma_str2int_concat_zeros(s, zeros);
}

exec fn multiply_binary(s1: &[char], s2: &[char]) -> (result: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@),
{
    let mut result = Vec::<char>::new();
    result.push('0');
    proof {
        assert(result@.len() == 1);
        assert(result@.index(0) == '0');
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == 0);
    }
    
    let mut shift_count: usize = 0;
    let mut i: usize = s2.len();
    
    while i > 0
        invariant
            0 <= i <= s2.len(),
            shift_count == s2.len() - i,
            ValidBitString(result@),
    {
        i = i - 1;
        
        if s2[i] == '1' {
            let mut partial = Vec::<char>::new();
            let mut j: usize = 0;
            while j < s1.len()
                invariant
                    0 <= j <= s1.len(),
                    ValidBitString(partial@),
                    partial@.len() == j,
                    forall |k: int| 0 <= k && k < j ==> partial@.index(k) == s1@.index(k),
            {
                partial.push(s1[j]);
                j = j + 1;
            }
            
            let mut k: usize = 0;
            while k < shift_count
                invariant
                    0 <= k <= shift_count,
                    ValidBitString(partial@),
            {
                partial.push('0');
                k = k + 1;
            }
            
            result = add_binary(&result, &partial);
        }
        
        shift_count = shift_count + 1;
    }
    
    result
}

exec fn add_binary(s1: &[char], s2: &[char]) -> (result: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@),
{
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            ValidBitString(result@),
            carry == 0 || carry == 1,
    {
        let mut sum = carry;
        
        if i < s1.len() {
            let idx = s1.len() - 1 - i;
            if s1[idx] == '1' {
                sum = sum + 1;
            }
        }
        
        if i < s2.len() {
            let idx = s2.len() - 1 - i;
            if s2[idx] == '1' {
                sum = sum + 1;
            }
        }
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        carry = sum / 2;
        i = i + 1;
    }
    
    reverse_vec(&result)
}

exec fn reverse_vec(v: &[char]) -> (result: Vec<char>)
    requires ValidBitString(v@),
    ensures
        ValidBitString(result@),
        result@.len() == v@.len(),
        forall |i: int| 0 <= i && i < v@.len() ==> result@.index(i) == v@.index(v@.len() - 1 - i),
{
    let mut result = Vec::<char>::new();
    let mut i: usize = v.len();
    
    while i > 0
        invariant
            0 <= i <= v.len(),
            ValidBitString(result@),
            result@.len() == v.len() - i,
            forall |j: int| 0 <= j && j < result@.len() ==> result@.index(j) == v@.index(v@.len() - 1 - j),
    {
        i = i - 1;
        result.push(v[i]);
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): Use actual multiplication implementation */
    if s1.len() == 0 || s2.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@.index(0) == '0');
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
            if s1.len() == 0 {
                assert(Str2Int(s1@) == 0);
            }
            if s2.len() == 0 {
                assert(Str2Int(s2@) == 0);
            }
            assert(0 * Str2Int(s2@) == 0);
            assert(Str2Int(s1@) * 0 == 0);
        }
        return result;
    }
    
    multiply_binary(s1, s2)
}
// </vc-code>

fn main() {}
}
