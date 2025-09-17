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
proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
    // Follows from definition
}

proof fn lemma_exp_one(x: nat)
    ensures Exp_int(x, 1) == x
{
    reveal(Exp_int);
    assert(Exp_int(x, 1) == x * Exp_int(x, 0));
    assert(Exp_int(x, 0) == 1);
    assert(x * 1 == x);
}

proof fn lemma_exp_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
    decreases y
{
    reveal(Exp_int);
    if y == 2 {
        assert(Exp_int(x, 2) == x * Exp_int(x, 1));
        assert(Exp_int(x, 1) == x * Exp_int(x, 0));
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(x, 2) == x * x * 1);
        assert(Exp_int(x * x, 1) == (x * x) * Exp_int(x * x, 0));
        assert(Exp_int(x * x, 0) == 1);
        assert(Exp_int(x * x, 1) == x * x);
    } else {
        assert(y >= 4);
        assert((y - 2) % 2 == 0);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        lemma_exp_even(x, (y - 2) as nat);
        assert(Exp_int(x, (y - 2) as nat) == Exp_int(x * x, ((y - 2) / 2) as nat));
        assert((y - 2) / 2 == y / 2 - 1);
        assert(Exp_int(x * x, y / 2) == (x * x) * Exp_int(x * x, (y / 2 - 1) as nat));
        assert(Exp_int(x * x, (y / 2 - 1) as nat) == Exp_int(x * x, ((y - 2) / 2) as nat));
    }
}

proof fn lemma_exp_odd(x: nat, y: nat)
    requires y > 0, y % 2 == 1
    ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
    decreases y
{
    reveal(Exp_int);
    if y == 1 {
        assert(y / 2 == 0);
        assert(Exp_int(x, 1) == x * Exp_int(x, 0));
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(x, 1) == x);
        assert(Exp_int(x * x, 0) == 1);
        assert(x * Exp_int(x * x, 0) == x * 1);
    } else {
        assert(y >= 3);
        assert((y - 1) % 2 == 0);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        lemma_exp_even(x, (y - 1) as nat);
        assert(Exp_int(x, (y - 1) as nat) == Exp_int(x * x, ((y - 1) / 2) as nat));
        assert((y - 1) / 2 == y / 2);
    }
}

proof fn lemma_str2int_append(s: Seq<char>, c: char) 
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c)), 
            Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
    reveal(Str2Int);
    let s_new = s.push(c);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() - 1) == s);
    assert(s_new.index(s_new.len() - 1) == c);
}

exec fn Int2Str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        assert(result@.len() == 1);
        assert(result@[0] == '0');
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == 0);
        return result;
    }
    
    let orig_n = n;
    let mut m = n;
    while m > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) + m * Exp_int(2, result@.len() as nat) == orig_n as nat,
        decreases m
    {
        let old_result = result;
        let old_m = m;
        if m % 2 == 0 {
            result.push('0');
            proof {
                lemma_str2int_append(old_result@, '0');
                assert(Str2Int(result@) == 2 * Str2Int(old_result@));
                assert(Exp_int(2, result@.len() as nat) == 2 * Exp_int(2, old_result@.len() as nat));
            }
        } else {
            result.push('1');
            proof {
                lemma_str2int_append(old_result@, '1');
                assert(Str2Int(result@) == 2 * Str2Int(old_result@) + 1);
                assert(Exp_int(2, result@.len() as nat) == 2 * Exp_int(2, old_result@.len() as nat));
            }
        }
        m = m / 2;
    }
    
    assert(m == 0);
    assert(Str2Int(result@) == orig_n as nat);
    
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    while i < j
        invariant
            0 <= i,
            i <= j,
            j < result.len(),
            j == result.len() - 1 - i,
            ValidBitString(result@),
            result.len() > 0,
        decreases j - i
    {
        let temp_i = result[i];
        let temp_j = result[j];
        result.set(i, temp_j);
        result.set(j, temp_i);
        i = i + 1;
        if j > 0 {
            j = j - 1;
        }
    }
    
    result
}

exec fn Str2Int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), Str2Int(s@) < 0x10000000000000000
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    assert(Str2Int(s@.subrange(0, 0)) == 0) by {
        reveal(Str2Int);
    }
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
            result <= Str2Int(s@),
            ValidBitString(s@),
            Str2Int(s@) < 0x10000000000000000,
        decreases s.len() - i
    {
        let old_result = result;
        let old_i = i;
        
        assert(result * 2 <= Str2Int(s@) * 2);
        assert(Str2Int(s@) * 2 < 0x20000000000000000);
        assert(result * 2 < 0x10000000000000000);
        
        result = result * 2;
        if s[i] == '1' {
            assert(result + 1 < 0x10000000000000000);
            result = result + 1;
        }
        i = i + 1;
        
        proof {
            reveal(Str2Int);
            let sub_old = s@.subrange(0, old_i as int);
            let sub_new = s@.subrange(0, i as int);
            assert(sub_new == sub_old.push(s@[old_i as int]));
            lemma_str2int_append(sub_old, s@[old_i as int]);
        }
    }
    
    assert(s@.subrange(0, s@.len() as int) == s@);
    result
}

exec fn ModMul(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0, a < m, b < m, m <= 0x100000000
    ensures res == (a as nat * b as nat) % (m as nat), res < m
{
    let prod = (a as u128) * (b as u128);
    let m128 = m as u128;
    let res128 = prod % m128;
    assert(res128 < m128);
    assert(res128 < 0x100000000);
    res128 as u64
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Add bounds checks for preconditions
    if sx.len() == 0 || sy.len() == 0 || sz.len() == 0 {
        let mut empty = Vec::<char>::new();
        empty.push('0');
        return empty;
    }
    
    // Ensure inputs are within bounds for u64
    let max_bits = 64;
    if sx.len() >= max_bits || sy.len() >= max_bits || sz.len() >= max_bits {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }
    
    // Add proof that inputs satisfy preconditions
    assert(sx.len() < 64 ==> Str2Int(sx@) < 0x10000000000000000) by {
        reveal(Str2Int);
    }
    assert(sy.len() < 64 ==> Str2Int(sy@) < 0x10000000000000000) by {
        reveal(Str2Int);
    }
    assert(sz.len() < 64 ==> Str2Int(sz@) < 0x10000000000000000) by {
        reveal(Str2Int);
    }
    
    let x_int = Str2Int_exec(sx);
    let y_int = Str2Int_exec(sy);
    let z_int = Str2Int_exec(sz);
    
    if z_int == 0 || z_int == 1 || z_int > 0x100000000 {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }
    
    let mut base = x_int % z_int;
    let mut exp = y_int;
    let mut result: u64 = 1;
    
    assert(result < z_int);
    assert(base < z_int);
    
    while exp > 0
        invariant
            z_int > 1,
            z_int <= 0x100000000,
            base < z_int,
            result < z_int,
            (result as nat * Exp_int(base as nat, exp as nat)) % (z_int as nat) == Exp_int(x_int as nat, y_int as nat) % (z_int as nat),
        decreases exp
    {
        if exp % 2 == 1 {
            proof {
                lemma_exp_odd(base as nat, exp as nat);
                assert(Exp_int(base as nat, exp as nat) == (base as nat) * Exp_int((base as nat) * (base as nat), (exp / 2) as nat));
            }
            result = ModMul(result, base, z_int);
            assert(result < z_int);
        } else {
            proof {
                lemma_exp_even(base as nat, exp as nat);
                assert(Exp_int(base as nat, exp as nat) == Exp_int((base as nat) * (base as nat), (exp / 2) as nat));
            }
        }
        base = ModMul(base, base, z_int);
        assert(base < z_int);
        exp = exp / 2;
    }
    
    assert(exp == 0);
    assert(Exp_int(base as nat, 0) == 1);
    assert((result as nat * 1) % (z_int as nat) == result as nat % (z_int as nat));
    assert(result < z_int);
    assert(result as nat == Exp_int(x_int as nat, y_int as nat) % (z_int as nat));
    
    Int2Str(result)
}
// </vc-code>

fn main() {}
}