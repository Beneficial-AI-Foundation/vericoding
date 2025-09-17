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
proof fn pow_mod_properties(x: nat, y: nat, z: nat)
    requires z > 1
    ensures
        y == 0 ==> Exp_int(x, y) % z == 1 % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

exec fn str_to_int_exec(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 64
    ensures res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            ValidBitString(s@)
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}

exec fn int_to_str_exec(mut n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    while n > 0
        invariant
            ValidBitString(result@),
            n as nat * Exp_int(2, result@.len() as nat) + Str2Int(result@) == old(n) as nat
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    while i < j
        invariant
            0 <= i <= j < result.len(),
            ValidBitString(result@)
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        if j > 0 { j = j - 1; }
    }
    result
}

exec fn mod_mult(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 1
    ensures res as nat == (a as nat * b as nat) % m as nat
{
    ((a % m) * (b % m)) % m
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let y_int = str_to_int_exec(sy);
    let z_int = str_to_int_exec(sz);
    let x_int = str_to_int_exec(sx);
    
    if y_int == 0 {
        proof { pow_mod_properties(x_int as nat, 0, z_int as nat); }
        return int_to_str_exec(1 % z_int);
    }
    
    let mut result = 1u64;
    let mut base = x_int % z_int;
    let mut exp = y_int;
    
    while exp > 0
        invariant
            z_int > 1,
            result as nat * Exp_int(base as nat, exp as nat) % z_int as nat == Exp_int(x_int as nat, y_int as nat) % z_int as nat,
            base as nat < z_int as nat
    {
        if exp % 2 == 1 {
            result = mod_mult(result, base, z_int);
        }
        base = mod_mult(base, base, z_int);
        exp = exp / 2;
        proof { pow_mod_properties(base as nat, exp as nat, z_int as nat); }
    }
    
    int_to_str_exec(result)
}
// </vc-code>

fn main() {}
}
