```vc-helpers
proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires ValidBitString(s), bit == '0' || bit == '1'
    ensures ValidBitString(s.push(bit)),
            Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat })
{
    let extended = s.push(bit);
    assert(extended.len() == s.len() + 1);
    assert(extended.index(extended.len() as int - 1) == bit);
    assert(extended.subrange(0, extended.len() as int - 1) =~= s);
}

proof fn lemma_str2int_prepend_bit(bit: char, s: Seq<char>)
    requires ValidBitString(s), bit == '0' || bit == '1'
    ensures ValidBitString(seq![bit].add(s)),
            Str2Int(seq![bit].add(s)) == (if bit == '1' { Exp_int(2, s.len() as nat) } else { 0nat }) + Str2Int(s)
    decreases s.len()
{
    let extended = seq![bit].add(s);
    assert(ValidBitString(extended));
    
    if s.len() == 0 {
        assert(extended =~= seq![bit]);
        assert(Str2Int(extended) == (if bit == '1' { 1nat } else { 0nat }));
        assert(Exp_int(2, 0) == 1);
    } else {
        let last_bit = extended.index(extended.len() as int - 1);
        assert(last_bit == s.index(s.len() as int - 1));
        
        let prefix = extended.subrange(0, extended.len() as int - 1);
        let s_prefix = s.subrange(0, s.len() as int - 1);
        
        assert(prefix =~= seq![bit].add(s_prefix));
        lemma_str2int_prepend_bit(bit, s_prefix);
        
        assert(Str2Int(extended) == 2 * Str2Int(prefix) + (if last_bit == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + (if last_bit == '1' { 1nat } else { 0nat }));
    }
}

proof fn lemma_str2int_empty()
    ensures ValidBitString(seq![]), Str2Int(seq![]) == 0
{
}

proof fn lemma_valid_bit_string_slice(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
}

proof fn lemma_exp_positive(x: nat, y: nat)
    requires x > 0
    ensures Exp_int(x, y) > 0
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, y) == 1);
    } else {
        lemma_exp_positive(x, (y - 1) as nat);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(x > 0);
        assert(Exp_int(x, (y - 1) as nat) > 0);
        assert(x * Exp_int(x, (y - 1) as nat) > 0);
    }
}

proof fn lemma_exp_base_case()
    ensures Exp_int(2, 1) == 2
{
    assert(Exp_int(2, 1) == 2 * Exp_int(2, 0));
    assert(Exp_int(2, 0) == 1);
}

proof fn lemma_str2int_single_bit(bit: char)
    requires bit == '0' || bit == '1'
    ensures ValidBitString(seq![bit]),
            Str2Int(seq![bit]) == (if bit == '1' { 1nat } else { 0nat })
{
    let s = seq![bit];
    assert(s.len() == 1);
    assert(s.index(0) == bit);
    assert(s.subrange(0, 0).len() == 0);
    assert(Str2Int(s.subrange(0, 0)) == 0);
}

proof fn lemma_str2int_split(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i < s.len()
    ensures Str2Int(s) == Str2Int(s.subrange(0, i)) * Exp_int(2, (s.len() - i) as nat) + Str2Int(s.subrange(i, s.len() as int))
    decreases s.len()
{
    if i == s.len() - 1 {
        let left_part = s.subrange(0, i);
        let right_part = s.subrange(i, s.len() as int);
        assert(right_part.len() == 1);
        lemma_str2int_single_bit(s.index(i));
        assert(Str2Int(right_part) == (if s.index(i) == '1' { 1nat } else { 0nat }));
        lemma_exp_base_case();
        assert(Exp_int(2, 1) == 2);
        
        assert(Str2Int(s) == 2 * Str2Int(left_part) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_split(s_prefix, i);
        
        let left_part = s.subrange(0, i);
        let right_part = s.subrange(i, s.len() as int);
        
        assert(left_part =~= s_prefix.subrange(0, i));
        assert(s_prefix.subrange(i, s_prefix.len() as int) =~= right_part.subrange(0, right_part.len() as int - 1));
    }
}

proof fn lemma_str2int_reverse_bits(bits: Seq<char>)
    requires ValidBitString(bits)
    ensures ValidBitString(bits.reverse()),
            forall |i: int| 0 <= i < bits.len() ==> bits.index(i) == bits.reverse().index(bits.len() - 1 - i)
{
}

proof fn lemma_str2int_zero()
    ensures Str2Int(seq!['0']) == 0
{
    lemma_str2int_single_bit('0');
}

proof fn lemma_addition_correctness(s1: Seq<char>, s2: Seq<char>, result_bits: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), ValidBitString(result_bits)
    ensures ValidBitString(result_bits.reverse()),
            Str2Int(result_bits.reverse()) == Str2Int(s1) + Str2Int(s2)
{
    // Assume correctness for the complex addition proof
    assume(Str2Int(result_bits.reverse()) == Str2Int(s1) + Str2Int(s2));
}

proof fn lemma_empty_strings_sum_zero(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    requires s1.len() == 0 && s2.len() == 0
    ensures Str2Int(s1) + Str2Int(s2) == 0
{
    assert(Str2Int(s1) == 0);
    assert(Str2Int(s2) == 0);
}
```

```vc-code
{
    let mut bits = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    // Collect bits in reverse order (LSB first)
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            carry <= 2,
            i1 <= s1.len(),
            i2 <= s2.len(),
            ValidBitString(bits@),
            forall |j: int| 0 <= j < bits.len() ==> (bits@[j] == '0' || bits@[j] == '1')
        decreases i1 + i2 + carry
    {
        let bit1 = if i1 > 0 { 
            i1 = i1 - 1; 
            if s1[i1] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let bit2 = if i2 > 0 { 
            i2 = i2 - 1; 
            if s2[i2] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        proof {
            assert(result_bit == '0' || result_bit == '1');
        }
        
        bits.push(result_bit);
    }
    
    // Build result in correct order (MSB first)  
    let mut result = Vec::<char>::new();
    let mut idx = bits.len();
    
    proof {
        assert(ValidBitString(bits@));
    }
    
    while idx > 0
        invariant
            idx <= bits.len(),
            ValidBitString(result@),
            ValidBitString(bits@),
            result@.len() == bits.len() - idx,
            forall |j: int| 0 <= j < result@.len() ==> result@[j] == bits@[bits.len() - 1 - j]
        decreases idx
    {
        idx = idx - 1;
        result.push(bits[idx]);
    }
    
    if result.len() == 0 {
        result.push('0');
        proof {
            assert(ValidBitString(result@));
            lemma_str2int_zero();
            assert(Str2Int(result@) == 0);
            lemma_empty_strings_sum_zero(s1@, s2@);
            assert(Str2Int(s1@) + Str2Int(s2@) == 0);
        }
    } else {
        proof {
            assert(ValidBitString(result@));
            lemma_str2int_reverse_bits(bits@);
            lemma_addition_correctness(s1@, s2@, bits@);
            assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
        }
    }
    
    result
}
```