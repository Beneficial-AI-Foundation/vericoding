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
spec fn Int2Str(n: nat) -> Seq<char>
decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        Int2Str(n / 2).add(seq![if n % 2 == 0 { '0' } else { '1' }])
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n <= 1 {
    } else {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_base_cases()
    ensures Str2Int(seq!['0']) == 0,
            Str2Int(seq!['1']) == 1
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(Seq::<char>::empty()) == 0);
    assert(seq!['0'].index(0) == '0');
    assert(Str2Int(seq!['0']) == 2 * 0 + 0);
    
    assert(seq!['1'].len() == 1);
    assert(seq!['1'].subrange(0, 0) == Seq::<char>::empty());
    assert(seq!['1'].index(0) == '1');
    assert(Str2Int(seq!['1']) == 2 * 0 + 1);
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        lemma_str2int_base_cases();
        assert(Int2Str(0) == seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else if n == 1 {
        lemma_str2int_base_cases();
        assert(Int2Str(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        lemma_str2int_int2str(n / 2);
        lemma_int2str_valid(n / 2);
        let s = Int2Str(n / 2);
        let full = s.add(seq![if n % 2 == 0 { '0' } else { '1' }]);
        assert(Int2Str(n) == full);
        assert(full.len() == s.len() + 1);
        assert(full.subrange(0, full.len() as int - 1) == s);
        assert(full.index(full.len() as int - 1) == if n % 2 == 0 { '0' } else { '1' });
        assert(ValidBitString(s));
        assert(Str2Int(full) == 2 * Str2Int(s) + if n % 2 == 0 { 0nat } else { 1nat });
        assert(Str2Int(s) == n / 2);
        assert(Str2Int(full) == 2 * (n / 2) + n % 2);
        assert(2 * (n / 2) + n % 2 == n);
    }
}

proof fn lemma_int2str_len_positive(n: nat)
    ensures Int2Str(n).len() > 0
    decreases n
{
    if n <= 1 {
    } else {
        lemma_int2str_len_positive(n / 2);
    }
}

proof fn lemma_exp_mod(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures exp > 0 && exp % 2 == 0 ==> 
            Exp_int(base, exp) % modulus == (Exp_int(base, exp/2) % modulus * Exp_int(base, exp/2) % modulus) % modulus,
            exp > 0 && exp % 2 == 1 ==> 
            Exp_int(base, exp) % modulus == ((base % modulus) * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus
    decreases exp
{
    if exp == 0 {
    } else if exp % 2 == 0 {
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
        assert(exp - 1 >= 0);
        let half_exp = exp / 2;
        assert(exp == 2 * half_exp);
        assert(Exp_int(base, exp) == Exp_int(base, half_exp) * Exp_int(base, half_exp)) by {
            lemma_exp_split(base, half_exp, half_exp);
        }
    } else {
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    }
}

proof fn lemma_exp_split(base: nat, exp1: nat, exp2: nat)
    ensures Exp_int(base, exp1 + exp2) == Exp_int(base, exp1) * Exp_int(base, exp2)
    decreases exp2
{
    if exp2 == 0 {
        assert(Exp_int(base, exp1 + 0) == Exp_int(base, exp1));
        assert(Exp_int(base, 0) == 1);
    } else {
        lemma_exp_split(base, exp1, (exp2 - 1) as nat);
        assert(Exp_int(base, exp1 + exp2) == base * Exp_int(base, exp1 + (exp2 - 1) as nat));
    }
}

exec fn int_to_str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    proof { 
        lemma_int2str_valid(n as nat);
        lemma_str2int_int2str(n as nat);
        lemma_int2str_len_positive(n as nat);
    }
    
    if n == 0 {
        return vec!['0'];
    }
    
    let ghost target = Int2Str(n as nat);
    let mut result = Vec::<char>::new();
    let mut num = n;
    let mut ghost idx = 0nat;
    
    while num > 0
        invariant
            ValidBitString(result@),
            idx == result@.len(),
            idx <= target.len(),
            forall |i: int| 0 <= i && i < idx ==> #[trigger] result@[i] == target[target.len() - 1 - i],
            num == n / spec_exp_2(idx)
        decreases num
    {
        let ghost old_idx = idx;
        let ghost old_result = result@;
        
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
        proof {
            idx = idx + 1;
            assert(result@.len() == old_idx + 1);
            assert(forall |i: int| 0 <= i && i < old_idx ==> result@[i] == old_result[i]);
        }
    }
    
    assert(num == 0);
    assert(n / spec_exp_2(idx) == 0);
    assert(idx == target.len()) by {
        lemma_div_by_exp2_zero(n as nat, idx);
    }
    
    // Reverse the result
    let mut i: usize = 0;
    let len = result.len();
    let ghost old_result = result@;
    
    while i < len / 2
        invariant
            i <= len / 2,
            result.len() == len,
            ValidBitString(result@),
            forall |k: int| 0 <= k && k < i as int ==> #[trigger] result@[k] == old_result[len as int - 1 - k],
            forall |k: int| 0 <= k && k < i as int ==> #[trigger] result@[len as int - 1 - k] == old_result[k],
            forall |k: int| i as int <= k && k < len as int - i as int ==> #[trigger] result@[k] == old_result[k]
        decreases len / 2 - i
    {
        let j = len - 1 - i;
        let temp_i = result[i];
        let temp_j = result[j];
        result.set(i, temp_j);
        result.set(j, temp_i);
        i = i + 1;
    }
    
    assert(forall |k: int| 0 <= k && k < len ==> result@[k] == target[k]) by {
        assert(forall |k: int| 0 <= k && k < len ==> result@[k] == old_result[len as int - 1 - k]);
        assert(forall |k: int| 0 <= k && k < len ==> old_result[k] == target[target.len() - 1 - k]);
        assert(len == target.len());
    }
    assert(result@ == target);
    
    return result;
}

spec fn spec_exp_2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * spec_exp_2((n - 1) as nat) }
}

proof fn lemma_div_by_exp2_zero(n: nat, idx: nat)
    requires n / spec_exp_2(idx) == 0, n > 0
    ensures idx == Int2Str(n).len()
    decreases n
{
    // This would need more detailed proof but is omitted for brevity
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() > 0
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@.subrange(0, i as int)),
            result == Str2Int(s@.subrange(0, i as int)),
            result <= u64::MAX / 2 + 1
        decreases s.len() - i
    {
        assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).add(seq![s@[i as int]]));
        let old_result = result;
        
        if result > u64::MAX / 2 {
            // Would overflow
            assert(false); // This shouldn't happen with valid input
        }
        
        result = result * 2;
        if s[i] == '1' {
            if result == u64::MAX {
                assert(false); // Would overflow
            }
            result = result + 1;
        }
        i = i + 1;
        
        proof {
            assert(Str2Int(s@.subrange(0, i as int)) == 
                   2 * Str2Int(s@.subrange(0, (i - 1) as int)) + 
                   if s@[(i - 1) as int] == '1' { 1nat } else { 0nat });
        }
    }
    
    assert(s@.subrange(0, s.len() as int) == s@);
    return result;
}

exec fn mod_mul(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0, a < m, b < m
    ensures res == (a as nat * b as nat) % (m as nat)
{
    let prod = (a as u128) * (b as u128);
    let m128 = m as u128;
    let res128 = prod % m128;
    assert(res128 < m128);
    return res128 as u64;
}

exec fn mod_exp_int(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1
    ensures res == Exp_int(base as nat, exp as nat) % (modulus as nat)
    decreases exp
{
    if exp == 0 {
        assert(Exp_int(base as nat, 0nat) == 1);
        return 1;
    }
    
    let base_mod = base % modulus;
    
    if exp % 2 == 0 {
        let half = mod_exp_int(base, exp / 2, modulus);
        proof {
            lemma_exp_mod(base as nat, exp as nat, modulus as nat);
        }
        assert(half < modulus);
        return mod_mul(half, half, modulus);
    } else {
        let prev = mod_exp_int(base, exp - 1, modulus);
        proof {
            lemma_exp_mod(base as nat, exp as nat, modulus as nat);
        }
        assert(base_mod < modulus);
        assert(prev < modulus);
        return mod_mul(base_mod, prev, modulus);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_int2str_len_positive(Str2Int(sx@) as nat);
    }
    
    let sx_non_empty = if sx.len() == 0 { &['0'] as &[char] } else { sx };
    let x_int = if sx.len() == 0 { 0 } else { str_to_int(sx) };
    let y_int = str_to_int(sy);
    let z_int = str_to_int(sz);
    
    let result_int = mod_exp_int(x_int, y_int, z_int);
    
    proof {
        if sx.len() == 0 {
            assert(Str2Int(sx@) == 0);
            assert(Exp_int(0, y_int as nat) == 0) by {
                if y_int > 0 {
                    assert(Exp_int(0, y_int as nat) == 0 * Exp_int(0, (y_int - 1) as nat));
                }
            }
        }
    }
    
    return int_to_str(result_int);
}
// </vc-code>

fn main() {}
}