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
    } else {
        let rest = Int2Str(n / 2);
        if n % 2 == 0 {
            rest.push('0')
        } else {
            rest.push('1')
        }
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n != 0 {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        assert(Int2Str(0) =~= seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else {
        lemma_str2int_int2str(n / 2);
        let rest = Int2Str(n / 2);
        if n % 2 == 0 {
            assert(Int2Str(n) =~= rest.push('0'));
            assert(Str2Int(rest.push('0')) == 2 * Str2Int(rest));
        } else {
            assert(Int2Str(n) =~= rest.push('1'));
            assert(Str2Int(rest.push('1')) == 2 * Str2Int(rest) + 1);
        }
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
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    
    let mut result = Vec::new();
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
    
    proof {
        assert(result@ =~= Int2Str(n as nat));
    }
    
    result
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() > 0, Str2Int(s@) < 0x10000000000000000
    ensures res == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 1 {
        if s[0] == '1' {
            return 1;
        } else {
            return 0;
        }
    }
    
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
            ValidBitString(s@.subrange(0, i as int)),
            result < 0x10000000000000000
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
        
        assert(s@.subrange(0, i as int) =~= s@.subrange(0, (i - 1) as int).push(s@[(i - 1) as int]));
    }
    
    assert(s@.subrange(0, s@.len() as int) =~= s@);
    result
}

exec fn mod_multiply(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0
    ensures res == (a as nat * b as nat) % (m as nat)
{
    ((a as u128 * b as u128) % m as u128) as u64
}

proof fn lemma_exp_recursive(x: nat, y: nat, m: nat)
    requires y > 0, m > 1
    ensures 
        if y % 2 == 0 {
            Exp_int(x, y) % m == Exp_int((x * x) % m, y / 2) % m
        } else {
            Exp_int(x, y) % m == (x * Exp_int((x * x) % m, y / 2)) % m
        }
    decreases y
{
    if y % 2 == 0 {
        assert(Exp_int(x, y) == Exp_int(x, y / 2) * Exp_int(x, y / 2));
        assert(Exp_int(x, y) % m == (Exp_int(x, y / 2) * Exp_int(x, y / 2)) % m);
    } else {
        assert(y == 2 * (y / 2) + 1);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == Exp_int(x, 2 * (y / 2)));
    }
}

exec fn is_zero_string(s: &[char]) -> (res: bool)
    requires ValidBitString(s@), s@.len() > 0
    ensures res <==> (Str2Int(s@) == 0)
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall |j: int| 0 <= j && j < i ==> s@[j] == '0'
    {
        if s[i] == '1' {
            return false;
        }
        i = i + 1;
    }
    true
}

exec fn div_by_two_string(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@), s@.len() > 0, Str2Int(s@) > 0
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@) / 2
{
    if s.len() == 1 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    
    let mut result = Vec::new();
    for i in 0..(s.len() - 1)
        invariant
            0 <= i <= s.len() - 1,
            ValidBitString(result@),
            result@.len() == i,
            forall |j: int| 0 <= j && j < i ==> result@[j] == s@[j]
    {
        result.push(s[i]);
    }
    
    if result.len() == 0 || !is_zero_string(&result) {
        result
    } else {
        let mut v = Vec::new();
        v.push('0');
        v
    }
}

exec fn is_odd_string(s: &[char]) -> (res: bool)
    requires ValidBitString(s@), s@.len() > 0
    ensures res <==> (Str2Int(s@) % 2 == 1)
{
    s[s.len() - 1] == '1'
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 || is_zero_string(sy) {
        let mut result = Vec::new();
        result.push('1');
        proof {
            lemma_int2str_valid(1nat);
            lemma_str2int_int2str(1nat);
            assert(Str2Int(result@) == 1);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        return result;
    }
    
    let x_val = str_to_int(sx);
    let z_val = str_to_int(sz);
    let x_mod = x_val % z_val;
    
    if sy.len() == 1 && sy[0] == '1' {
        let res_val = x_mod;
        let result = int_to_str(res_val);
        proof {
            assert(Str2Int(sy@) == 1);
            assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@));
            assert(Str2Int(result@) == x_val % z_val);
        }
        return result;
    }
    
    let sy_half = div_by_two_string(sy);
    let x_squared = mod_multiply(x_mod, x_mod, z_val);
    let x_squared_str = int_to_str(x_squared);
    
    let half_result = ModExp_Mul_Zeroes(&x_squared_str, &sy_half, sz);
    let half_val = str_to_int(&half_result);
    
    let res_val = if is_odd_string(sy) {
        mod_multiply(x_mod, half_val, z_val)
    } else {
        half_val
    };
    
    let result = int_to_str(res_val);
    
    proof {
        lemma_exp_recursive(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        assert(sy_half@.len() < sy@.len());
    }
    
    result
}
// </vc-code>

fn main() {}
}