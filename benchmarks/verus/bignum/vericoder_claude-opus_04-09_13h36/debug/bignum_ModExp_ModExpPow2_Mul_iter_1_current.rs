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

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        assert(Int2Str(0) == seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else if n == 1 {
        assert(Int2Str(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        let full = s.add(seq![if n % 2 == 0 { '0' } else { '1' }]);
        assert(Int2Str(n) == full);
        assert(full.len() == s.len() + 1);
        assert(full.subrange(0, full.len() as int - 1) == s);
        assert(full.index(full.len() as int - 1) == if n % 2 == 0 { '0' } else { '1' });
        assert(Str2Int(full) == 2 * Str2Int(s) + if n % 2 == 0 { 0 } else { 1 });
        assert(Str2Int(s) == n / 2);
        assert(Str2Int(full) == 2 * (n / 2) + n % 2);
        assert(2 * (n / 2) + n % 2 == n);
    }
}

exec fn int_to_str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    proof { 
        lemma_int2str_valid(n as nat);
        lemma_str2int_int2str(n as nat);
    }
    
    if n == 0 {
        return vec!['0'];
    }
    
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    while num > 0
        invariant
            ValidBitString(result@),
            forall |i: int| 0 <= i && i < result@.len() ==> result@[i] == Int2Str(n as nat)[i],
            result@.len() <= Int2Str(n as nat).len()
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    // Reverse the result
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    
    while i < j
        invariant
            i <= j,
            j < result.len(),
            ValidBitString(result@)
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
    
    return result;
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
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    assert(s@.subrange(0, s.len() as int) == s@);
    return result;
}

exec fn mod_mul(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0
    ensures res == (a as nat * b as nat) % m
{
    return ((a as u128 * b as u128) % (m as u128)) as u64;
}

exec fn mod_exp_int(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1
    ensures res == Exp_int(base as nat, exp as nat) % modulus
    decreases exp
{
    if exp == 0 {
        return 1;
    }
    
    if exp % 2 == 0 {
        let half = mod_exp_int(base, exp / 2, modulus);
        return mod_mul(half, half, modulus);
    } else {
        let prev = mod_exp_int(base, exp - 1, modulus);
        return mod_mul(base, prev, modulus);
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
    let x_int = str_to_int(sx);
    let y_int = str_to_int(sy);
    let z_int = str_to_int(sz);
    
    let result_int = mod_exp_int(x_int, y_int, z_int);
    
    return int_to_str(result_int);
}
// </vc-code>

fn main() {}
}