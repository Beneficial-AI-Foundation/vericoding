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
        Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat }),
    decreases s.len()
{
    let s_new = s.push(bit);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
}

proof fn lemma_mul_by_power_of_2(s: Seq<char>, k: nat)
    requires
        ValidBitString(s),
    ensures
        Str2Int(seq_repeat_zero(k) + s) == pow2(k) * Str2Int(s),
    decreases k
{
    if k == 0 {
        assert(seq_repeat_zero(0) + s == s);
    } else {
        let zeros = seq_repeat_zero(k);
        let prev_zeros = seq_repeat_zero((k - 1) as nat);
        assert(zeros == prev_zeros.push('0'));
        lemma_mul_by_power_of_2(s, (k - 1) as nat);
        lemma_str2int_append_bit(prev_zeros + s, '0');
        assert(Str2Int(zeros + s) == 2 * Str2Int(prev_zeros + s));
        lemma_pow2_unfold(k);
    }
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
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to main loop */
    let mut result = Vec::<char>::new();
    let mut partial_sum = Vec::<char>::new();
    partial_sum.push('0');
    
    let mut i: usize = 0;
    while i < s2.len()
        invariant
            i <= s2.len(),
            ValidBitString(partial_sum@),
            Str2Int(partial_sum@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, i as int)),
        decreases s2.len() - i
    {
        if s2[i] == '1' {
            let mut shifted = Vec::<char>::new();
            let mut j: usize = 0;
            while j < s1.len()
                invariant
                    j <= s1.len(),
                    ValidBitString(shifted@),
                    shifted@.len() == j,
                    forall |k: int| 0 <= k && k < j ==> shifted@.index(k) == s1@.index(k),
                decreases s1.len() - j
            {
                shifted.push(s1[j]);
                j = j + 1;
            }
            
            let mut k: usize = 0;
            while k < (s2.len() - i - 1)
                invariant
                    k <= s2.len() - i - 1,
                    ValidBitString(shifted@),
                    shifted@.len() == s1.len() + k,
                decreases s2.len() - i - 1 - k
            {
                shifted.push('0');
                k = k + 1;
            }
            
            proof {
                lemma_mul_by_power_of_2(s1@, (s2.len() - i - 1) as nat);
            }
            
            partial_sum = add_binary_strings(&partial_sum, &shifted);
        }
        i = i + 1;
    }
    
    result = partial_sum;
    result
}

exec fn add_binary_strings(s1: &Vec<char>, s2: &Vec<char>) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@),
{
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 1,
        decreases max_len - i + carry
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
    }
    
    let mut reversed = Vec::<char>::new();
    let mut j: usize = 0;
    while j < result.len()
        invariant
            j <= result.len(),
            ValidBitString(reversed@),
            reversed@.len() == j,
        decreases result.len() - j
    {
        reversed.push(result[result.len() - 1 - j]);
        j = j + 1;
    }
    
    reversed
}
// </vc-code>

fn main() {}
}
