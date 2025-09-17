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
/* helper modified by LLM (iteration 4): Fixed range syntax error in str_to_nat function */
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
        exp_even(x, (y - 2) as nat);
    }
}

exec fn compute_mod(a: u64, m: u64) -> (res: u64)
    requires m > 0
    ensures res == a % m, res < m
{
    a % m
}

exec fn str_to_nat(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    ensures res as nat == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix_len = (s.len() - 1) as usize;
        let prefix = &s[..prefix_len];
        let last = s[s.len() - 1];
        let prefix_val = str_to_nat(prefix);
        2 * prefix_val + (if last == '1' { 1 } else { 0 })
    }
}

exec fn nat_to_str(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat
    decreases n
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    let ghost orig_n = n;
    while n > 0
        invariant
            ValidBitString(result@),
            n as nat + Str2Int(result@) == orig_n as nat,
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

exec fn mod_exp_helper(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1
    ensures res as nat == Exp_int(base as nat, exp as nat) % (modulus as nat)
    decreases exp
{
    if exp == 0 {
        1
    } else if exp == 1 {
        compute_mod(base, modulus)
    } else if exp % 2 == 0 {
        proof { exp_even(base as nat, exp as nat); }
        let half_exp = exp / 2;
        let sqrt_res = mod_exp_helper(base, half_exp, modulus);
        let squared = compute_mod(sqrt_res * sqrt_res, modulus);
        proof { pow_mod_square(Exp_int(base as nat, half_exp as nat), modulus as nat); }
        squared
    } else {
        proof { exp_split(base as nat, exp as nat); }
        let sub_res = mod_exp_helper(base, exp - 1, modulus);
        let result = compute_mod(base * sub_res, modulus);
        proof { pow_mod_mul(base as nat, Exp_int(base as nat, (exp - 1) as nat), (base as nat) * Exp_int(base as nat, (exp - 1) as nat), modulus as nat); }
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
    /* code modified by LLM (iteration 4): No changes needed to main code */
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
