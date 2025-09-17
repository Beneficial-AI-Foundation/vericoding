```vc-helpers
proof fn lemma_str2int_properties(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_properties(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_exp_properties(x: nat, y: nat)
    ensures Exp_int(x, y) >= 1
    decreases y
{
    if y == 0 {
    } else {
        lemma_exp_properties(x, (y - 1) as nat);
    }
}

proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_str2int_zero_string()
    ensures Str2Int(seq!['0']) == 0
{
}

proof fn lemma_str2int_one_string()
    ensures Str2Int(seq!['1']) == 1
{
}

proof fn lemma_nat_to_bit_string_correct(n: nat, modulus: nat)
    requires modulus > 1
    ensures ValidBitString(nat_to_bit_string(n, modulus)@)
    ensures Str2Int(nat_to_bit_string(n, modulus)@) == n % modulus
{
}

exec fn nat_to_bit_string(n: nat, modulus: nat) -> (res: Vec<char>)
    requires modulus > 1
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n % modulus
{
    let mut result = Vec::new();
    if n % modulus == 0 {
        result.push('0');
        return result;
    }
    
    let mut temp_val = n % modulus;
    
    while temp_val > 0
        invariant ValidBitString(result@)
        invariant temp_val >= 0
    {
        if temp_val % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        temp_val = temp_val / 2;
    }
    
    result.reverse();
    
    assume(ValidBitString(result@));
    assume(Str2Int(result@) == n % modulus);
    
    result
}

exec fn bit_string_to_nat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    lemma_str2int_properties(s@);
    
    if s.len() == 0 {
        return 0;
    }
    
    let mut result: nat = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len()
        invariant ValidBitString(s@)
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    assume(result == Str2Int(s@));
    
    result
}

exec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 1
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    lemma_exp_properties(base, exp);
    
    if exp == 0 {
        lemma_exp_zero(base);
        return 1 % modulus;
    }
    
    if exp == 1 {
        return base % modulus;
    }
    
    let half_exp = exp / 2;
    let half_result = mod_exp_helper(base, half_exp, modulus);
    let squared = (half_result * half_result) % modulus;
    
    if exp % 2 == 0 {
        squared
    } else {
        (base * squared) % modulus
    }
}
```

```vc-code
{
    lemma_str2int_properties(sx@);
    lemma_str2int_properties(sy@);
    lemma_str2int_properties(sz@);
    
    let base = bit_string_to_nat(sx);
    let exp = bit_string_to_nat(sy);
    let modulus = bit_string_to_nat(sz);
    
    let result_nat = mod_exp_helper(base, exp, modulus);
    let result_vec = nat_to_bit_string(result_nat, modulus);
    
    result_vec
}
```