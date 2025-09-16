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
/* helper modified by LLM (iteration 5): Added comprehensive lemmas for multiplication properties and bit string manipulation */
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s)
    decreases s.len()
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == '1');
}

proof fn lemma_str2int_zero()
    ensures
        Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    let empty: Seq<char> = seq![];
    assert(seq!['0'].subrange(0, 0) == empty);
    assert(Str2Int(empty) == 0);
}

proof fn lemma_str2int_one()
    ensures
        Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].len() == 1);
    let empty: Seq<char> = seq![];
    assert(seq!['1'].subrange(0, 0) == empty);
    assert(Str2Int(empty) == 0);
}

proof fn lemma_all_zeros(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0'
    ensures
        Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == '0');
        lemma_str2int_zero();
        assert(Str2Int(s) == 0);
    } else {
        let prefix = s.subrange(0, s.len() - 1);
        assert(forall |i: int| 0 <= i && i < prefix.len() ==> prefix[i] == s[i]);
        assert(forall |i: int| 0 <= i && i < prefix.len() ==> prefix[i] == '0');
        lemma_all_zeros(prefix);
        assert(Str2Int(prefix) == 0);
        assert(s[s.len() - 1] == '0');
        assert(Str2Int(s) == 2 * Str2Int(prefix) + 0);
        assert(Str2Int(s) == 2 * 0 + 0);
        assert(Str2Int(s) == 0);
    }
}

proof fn lemma_empty_string()
    ensures
        Str2Int(seq![]) == 0
{
    assert(seq![].len() == 0);
}

proof fn lemma_mult_by_zero(a: nat)
    ensures
        a * 0 == 0,
        0 * a == 0
{
    assert(a * 0 == 0);
    assert(0 * a == 0);
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified multiplication using binary representation */
    let mut result = Vec::<char>::new();
    
    // Handle empty inputs
    if s1.len() == 0 || s2.len() == 0 {
        result.push('0');
        proof {
            lemma_str2int_zero();
            lemma_empty_string();
            if s1.len() == 0 {
                assert(Str2Int(s1@) == 0);
            }
            if s2.len() == 0 {
                assert(Str2Int(s2@) == 0);
            }
            lemma_mult_by_zero(if s1.len() == 0 { Str2Int(s2@) } else { Str2Int(s1@) });
            assert(Str2Int(s1@) * Str2Int(s2@) == 0);
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
        }
        return result;
    }
    
    // Check if s1 is all zeros
    let mut is_zero_s1 = true;
    let mut i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            is_zero_s1 == (forall |j: int| 0 <= j && j < i ==> s1@[j] == '0'),
        decreases s1.len() - i
    {
        if s1[i] != '0' {
            is_zero_s1 = false;
        }
        i = i + 1;
    }
    
    if is_zero_s1 {
        result.push('0');
        proof {
            lemma_str2int_zero();
            assert(forall |j: int| 0 <= j && j < s1.len() ==> s1@[j] == '0');
            lemma_all_zeros(s1@);
            assert(Str2Int(s1@) == 0);
            lemma_mult_by_zero(Str2Int(s2@));
            assert(Str2Int(s1@) * Str2Int(s2@) == 0);
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
        }
        return result;
    }
    
    // Check if s2 is all zeros
    let mut is_zero_s2 = true;
    let mut i = 0;
    while i < s2.len()
        invariant
            0 <= i <= s2.len(),
            is_zero_s2 == (forall |j: int| 0 <= j && j < i ==> s2@[j] == '0'),
        decreases s2.len() - i
    {
        if s2[i] != '0' {
            is_zero_s2 = false;
        }
        i = i + 1;
    }
    
    if is_zero_s2 {
        result.push('0');
        proof {
            lemma_str2int_zero();
            assert(forall |j: int| 0 <= j && j < s2.len() ==> s2@[j] == '0');
            lemma_all_zeros(s2@);
            assert(Str2Int(s2@) == 0);
            lemma_mult_by_zero(Str2Int(s1@));
            assert(Str2Int(s1@) * Str2Int(s2@) == 0);
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
        }
        return result;
    }
    
    // Simple O(n*m) multiplication: multiply s1 by each bit of s2
    // Initialize result with '0'
    result.push('0');
    proof {
        lemma_str2int_zero();
        assert(Str2Int(result@) == 0);
    }
    
    let mut bit_idx: usize = 0;
    while bit_idx < s2.len()
        invariant
            0 <= bit_idx <= s2.len(),
            ValidBitString(result@),
        decreases s2.len() - bit_idx
    {
        if s2[s2.len() - 1 - bit_idx] == '1' {
            // Add s1 shifted left by bit_idx to result
            let mut carry: u8 = 0;
            let mut res_idx: usize = 0;
            let max_idx = if s1.len() > bit_idx { s1.len() } else { bit_idx + 1 };
            
            while res_idx < max_idx
                invariant
                    0 <= res_idx <= max_idx,
                    carry <= 1,
                    ValidBitString(result@),
                decreases max_idx - res_idx
            {
                let s1_bit: u8 = if res_idx >= bit_idx && res_idx - bit_idx < s1.len() {
                    if s1[s1.len() - 1 - (res_idx - bit_idx)] == '1' { 1 } else { 0 }
                } else {
                    0
                };
                
                let res_bit: u8 = if res_idx < result.len() {
                    if result[result.len() - 1 - res_idx] == '1' { 1 } else { 0 }
                } else {
                    0
                };
                
                let sum: u8 = s1_bit + res_bit + carry;
                let new_bit: char = if sum % 2 == 1 { '1' } else { '0' };
                carry = sum / 2;
                
                if res_idx < result.len() {
                    result.set(result.len() - 1 - res_idx, new_bit);
                } else {
                    let mut new_result = Vec::<char>::new();
                    new_result.push(new_bit);
                    let mut j: usize = 0;
                    while j < result.len()
                        invariant
                            0 <= j <= result.len(),
                            new_result@.len() == j + 1,
                            new_result@[0] == new_bit,
                            forall |k: int| 1 <= k && k < j + 1 ==> (new_result@[k] == '0' || new_result@[k] == '1'),
                            forall |k: int| 1 <= k && k < j + 1 ==> new_result@[k] == result@[k - 1],
                        decreases result.len() - j
                    {
                        new_result.push(result[j]);
                        j = j + 1;
                    }
                    proof {
                        assert(ValidBitString(result@));
                        assert(forall |k: int| 0 <= k && k < result.len() ==> (result@[k] == '0' || result@[k] == '1'));
                        assert(new_result@[0] == new_bit);
                        assert(new_bit == '0' || new_bit == '1');
                        assert(forall |k: int| 1 <= k && k < new_result@.len() ==> new_result@[k] == result@[k - 1]);
                        assert(forall |k: int| 0 <= k && k < new_result@.len() ==> (new_result@[k] == '0' || new_result@[k] == '1'));
                        assert(ValidBitString(new_result@));
                    }
                    result = new_result;
                }
                
                res_idx = res_idx + 1;
            }
            
            if carry == 1 {
                let mut new_result = Vec::<char>::new();
                new_result.push('1');
                let mut j: usize = 0;
                while j < result.len()
                    invariant
                        0 <= j <= result.len(),
                        new_result@.len() == j + 1,
                        new_result@[0] == '1',
                        forall |k: int| 1 <= k && k < j + 1 ==> (new_result@[k] == '0' || new_result@[k] == '1'),
                        forall |k: int| 1 <= k && k < j + 1 ==> new_result@[k] == result@[k - 1],
                    decreases result.len() - j
                {
                    new_result.push(result[j]);
                    j = j + 1;
                }
                proof {
                    assert(ValidBitString(result@));
                    assert(forall |k: int| 0 <= k && k < result.len() ==> (result@[k] == '0' || result@[k] == '1'));
                    assert(new_result@[0] == '1');
                    assert(forall |k: int| 1 <= k && k < new_result@.len() ==> new_result@[k] == result@[k - 1]);
                    assert(forall |k: int| 0 <= k && k < new_result@.len() ==> (new_result@[k] == '0' || new_result@[k] == '1'));
                    assert(ValidBitString(new_result@));
                }
                result = new_result;
            }
        }
        
        bit_idx = bit_idx + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
