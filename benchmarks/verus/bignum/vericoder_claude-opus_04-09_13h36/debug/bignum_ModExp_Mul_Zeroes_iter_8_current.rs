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
    if n > 1 {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_subrange(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i <= s.len()
    ensures ValidBitString(s.subrange(0, i))
{
}

proof fn lemma_str2int_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures 
        ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat }
    decreases s.len()
{
    assert(s.push(c).len() == s.len() + 1);
    assert(s.push(c).subrange(0, s.push(c).len() - 1) =~= s);
    assert(s.push(c).index(s.push(c).len() - 1) == c);
}

proof fn lemma_str2int_int2str(n: nat)
    ensures 
        ValidBitString(Int2Str(n)),
        Str2Int(Int2Str(n)) == n
    decreases n
{
    lemma_int2str_valid(n);
    if n == 0 {
        assert(Int2Str(0) =~= seq!['0']);
    } else if n == 1 {
        assert(Int2Str(1) =~= seq!['1']);
    } else {
        lemma_str2int_int2str(n / 2);
        let rest = Int2Str(n / 2);
        lemma_int2str_valid(n / 2);
        if n % 2 == 0 {
            lemma_str2int_push(rest, '0');
            assert(Int2Str(n) =~= rest.push('0'));
        } else {
            lemma_str2int_push(rest, '1');
            assert(Int2Str(n) =~= rest.push('1'));
        }
    }
}

pub exec fn int_to_str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    proof { 
        lemma_str2int_int2str(n as nat);
    }
    
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        assert(v@ =~= seq!['0']);
        return v;
    }
    
    if n == 1 {
        let mut v = Vec::new();
        v.push('1');
        assert(v@ =~= seq!['1']);
        return v;
    }
    
    let half = int_to_str(n / 2);
    let mut result = half;
    if n % 2 == 0 {
        result.push('0');
    } else {
        result.push('1');
    }
    
    proof {
        lemma_str2int_push(half@, if n % 2 == 0 { '0' } else { '1' });
    }
    
    result
}

pub exec fn str_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() > 0, Str2Int(s@) < 0x10000000000000000
    ensures res == Str2Int(s@)
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
            ValidBitString(s@.subrange(0, i as int)),
            result == Str2Int(s@.subrange(0, i as int)),
            result < 0x10000000000000000,
            2 * result < 0x10000000000000000
    {
        proof {
            lemma_str2int_subrange(s@, (i + 1) as int);
            assert(s@.subrange(0, (i + 1) as int) =~= s@.subrange(0, i as int).push(s@[i as int]));
            lemma_str2int_push(s@.subrange(0, i as int), s@[i as int]);
        }
        
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    assert(s@.subrange(0, s@.len() as int) =~= s@);
    result
}

pub exec fn mod_multiply(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0, a < m, b < m
    ensures res == (a as nat * b as nat) % (m as nat)
{
    let product = (a as u128) * (b as u128);
    let modulo = (m as u128);
    ((product % modulo) as u64)
}

proof fn lemma_exp_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x, y / 2) * Exp_int(x, y / 2)
    decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * x);
        assert(Exp_int(x, 1) == x);
    } else {
        lemma_exp_even(x, (y / 2) as nat);
        assert(y == 2 * (y / 2));
    }
}

proof fn lemma_exp_odd(x: nat, y: nat)
    requires y > 0, y % 2 == 1
    ensures Exp_int(x, y) == x * Exp_int(x, y / 2) * Exp_int(x, y / 2)
    decreases y
{
    if y == 1 {
        assert(Exp_int(x, 1) == x);
        assert(Exp_int(x, 0) == 1);
    } else {
        assert(y == 2 * (y / 2) + 1);
        lemma_exp_even(x, ((y - 1) as nat));
    }
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
        lemma_exp_even(x, y);
    } else {
        lemma_exp_odd(x, y);
    }
}

pub exec fn is_zero_string(s: &[char]) -> (res: bool)
    requires ValidBitString(s@), s@.len() > 0
    ensures res <==> (Str2Int(s@) == 0)
{
    if s.len() == 1 {
        return s[0] == '0';
    }
    
    let mut all_zero = true;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            all_zero <==> (forall |j: int| 0 <= j && j < i ==> s@[j] == '0')
    {
        if s[i] == '1' {
            all_zero = false;
        }
        i = i + 1;
    }
    
    proof {
        if all_zero {
            assert(forall |j: int| 0 <= j && j < s@.len() ==> s@[j] == '0');
        }
    }
    
    all_zero
}

pub exec fn div_by_two_string(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@), s@.len() > 0, Str2Int(s@) > 0
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@) / 2
{
    if s.len() == 1 {
        let mut v = Vec::new();
        v.push('0');
        assert(v@ =~= seq!['0']);
        return v;
    }
    
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len() - 1
        invariant
            0 <= i <= s.len() - 1,
            ValidBitString(result@),
            result@.len() == i,
            forall |j: int| 0 <= j && j < i ==> result@[j] == s@[j]
    {
        result.push(s[i]);
        i = i + 1;
    }
    
    proof {
        assert(result@ =~= s@.subrange(0, s@.len() - 1));
        lemma_str2int_subrange(s@, s@.len() - 1);
    }
    
    if result.len() > 0 && !is_zero_string(&result) {
        result
    } else {
        let mut v = Vec::new();
        v.push('0');
        v
    }
}

pub exec fn is_odd_string(s: &[char]) -> (res: bool)
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
    if is_zero_string(sy) {
        let mut result = Vec::new();
        result.push('1');
        proof {
            assert(Str2Int(result@) == 1);
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        return result;
    }
    
    let x_val = str_to_int(sx);
    let z_val = str_to_int(sz);
    let x_mod = x_val % z_val;
    
    if sy.len() == 1 && sy[0] == '1' {
        let result = int_to_str(x_mod);
        proof {
            assert(Str2Int(sy@) == 1);
            assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@));
            assert(Str2Int(result@) == x_val % z_val);
            assert(Str2Int(result@) == Str2Int(sx@) % Str2Int(sz@));
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
        assert(Str2Int(sy_half@) == Str2Int(sy@) / 2);
        assert(x_squared == (x_mod as nat * x_mod as nat) % (z_val as nat));
        assert(Str2Int(x_squared_str@) == x_squared);
        assert(Str2Int(half_result@) == Exp_int(x_squared as nat, Str2Int(sy_half@)) % (z_val as nat));
        
        if is_odd_string(sy) {
            assert(Str2Int(sy@) % 2 == 1);
            assert(res_val == (x_mod as nat * half_val as nat) % (z_val as nat));
        } else {
            assert(Str2Int(sy@) % 2 == 0);
            assert(res_val == half_val);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}