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
proof fn pow_mod_mul(a: nat, b: nat, c: nat, m: nat)
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn pow_mod_square(a: nat, m: nat)
    requires m > 1
    ensures (a * a) % m == ((a % m) * (a % m)) % m
{
}

proof fn exp_split(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn exp_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
    decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * x);
        assert(Exp_int(x * x, 1) == x * x);
    } else {
        let half = y / 2;
        assert(y == 2 * half);
        exp_even(x, y - 2);
    }
}

exec fn compute_mod(a: nat, m: nat) -> (res: nat)
    requires m > 0
    ensures res == a % m, res < m
{
    (a % m) as nat
}

exec fn str_to_nat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0nat
    } else {
        let prefix = &s[..s.len() - 1];
        let last = s[s.len() - 1];
        let prefix_val = str_to_nat(prefix);
        2 * prefix_val + (if last == '1' { 1nat } else { 0nat })
    }
}

exec fn nat_to_str(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
    decreases n
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant
            ValidBitString(result@),
            n + Str2Int(result@) == old(n),
        decreases n
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    
    result.reverse();
    result
}

exec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 1
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        1nat
    } else if exp == 1 {
        compute_mod(base, modulus)
    } else if exp % 2 == 0 {
        proof { exp_even(base, exp); }
        let half_exp = exp / 2;
        let sqrt_res = mod_exp_helper(base, half_exp, modulus);
        let squared = compute_mod(sqrt_res * sqrt_res, modulus);
        proof { pow_mod_square(Exp_int(base, half_exp), modulus); }
        squared
    } else {
        proof { exp_split(base, exp); }
        let sub_res = mod_exp_helper(base, (exp - 1) as nat, modulus);
        let result = compute_mod(base * sub_res, modulus);
        proof { pow_mod_mul(base, Exp_int(base, (exp - 1) as nat), base * Exp_int(base, (exp - 1) as nat), modulus); }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = str_to_nat(sx);
    let y_val = str_to_nat(sy);
    let z_val = str_to_nat(sz);
    
    let result_val = mod_exp_helper(x_val, y_val, z_val);
    let result = nat_to_str(result_val);
    
    result
}
// </vc-code>

fn main() {}
}
