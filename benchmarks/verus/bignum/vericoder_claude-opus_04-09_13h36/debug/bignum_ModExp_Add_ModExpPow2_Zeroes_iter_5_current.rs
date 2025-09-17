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
}

proof fn lemma_exp_one(x: nat)
    ensures Exp_int(x, 1) == x
{
    assert(Exp_int(x, 1) == x * Exp_int(x, 0));
    assert(Exp_int(x, 0) == 1);
}

proof fn lemma_exp_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
    decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * x * 1);
        assert(Exp_int(x * x, 1) == x * x);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == x * Exp_int(x, (y - 2) as nat));
        lemma_exp_even(x, (y - 2) as nat);
    }
}

proof fn lemma_exp_odd(x: nat, y: nat)
    requires y > 0, y % 2 == 1
    ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
    decreases y
{
    if y == 1 {
        assert(Exp_int(x, 1) == x);
        assert(Exp_int(x * x, 0) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        lemma_exp_even(x, (y - 1) as nat);
    }
}

exec fn Int2Str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    let orig_n = n;
    let mut m = n;
    while m > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) + m * Exp_int(2, result@.len() as nat) == orig_n as nat,
    {
        if m % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        m = m / 2;
    }
    
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    while i < j
        invariant
            0 <= i <= j < result.len(),
            j == result.len() - 1 - i,
            ValidBitString(result@),
            Str2Int(result@) == orig_n as nat,
    {
        let temp_i = result[i];
        let temp_j = result[j];
        result.set(i, temp_j);
        result.set(j, temp_i);
        i = i + 1;
        j = j - 1;
    }
    
    result
}

exec fn Str2Int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), Str2Int(s@) < 0x10000000000000000
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
            ValidBitString(s@),
            Str2Int(s@) < 0x10000000000000000,
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    result
}

exec fn ModMul(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0, a < m, b < m
    ensures res == (a as nat * b as nat) % (m as nat), res < m
{
    ((a as u128 * b as u128) % m as u128) as u64
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
    let x_int = Str2Int_exec(sx);
    let y_int = Str2Int_exec(sy);
    let z_int = Str2Int_exec(sz);
    
    let mut base = x_int % z_int;
    let mut exp = y_int;
    let mut result: u64 = 1;
    
    while exp > 0
        invariant
            z_int > 1,
            base < z_int,
            result < z_int,
            (result as nat * Exp_int(base as nat, exp as nat)) % (z_int as nat) == Exp_int(x_int as nat, y_int as nat) % (z_int as nat),
    {
        if exp % 2 == 1 {
            proof {
                lemma_exp_odd(base as nat, exp as nat);
            }
            result = ModMul(result, base, z_int);
        } else {
            proof {
                lemma_exp_even(base as nat, exp as nat);
            }
        }
        base = ModMul(base, base, z_int);
        exp = exp / 2;
    }
    
    Int2Str(result)
}
// </vc-code>

fn main() {}
}