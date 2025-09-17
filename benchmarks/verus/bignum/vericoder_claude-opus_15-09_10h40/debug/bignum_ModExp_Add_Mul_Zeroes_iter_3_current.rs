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
proof fn exp_mod_properties()
    ensures
        forall|x: nat, n: nat| n > 0 ==> #[trigger] Exp_int(x, 0) % n == 1nat % n,
        forall|x: nat, y: nat, n: nat| n > 0 && y > 0 ==> #[trigger] Exp_int(x, y) % n == ((x % n) * (Exp_int(x, (y - 1) as nat) % n)) % n,
{}

/* helper modified by LLM (iteration 3): Fixed return value naming in ensures clause */
fn int_to_binary(mut n: u64) -> (result: Vec<char>)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n,
{
    let ghost old_n = n;
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    while n > 0
        invariant
            ValidBitString(result@),
            n + Str2Int(result@) * Exp_int(2, result@.len() as nat) == old_n,
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    result
}

fn mod_mult(x: u64, y: u64, m: u64) -> u64
    requires
        m > 0,
        x < m,
        y < m,
    ensures
        mod_mult(x, y, m) == ((x as int) * (y as int)) % (m as int),
        mod_mult(x, y, m) < m,
{
    ((x % m) * (y % m)) % m
}

fn mod_exp(base: u64, exp: u64, modulus: u64) -> u64
    requires
        modulus > 1,
        base < modulus,
    ensures
        mod_exp(base, exp, modulus) == Exp_int(base as nat, exp as nat) % (modulus as nat),
        mod_exp(base, exp, modulus) < modulus,
    decreases exp,
{
    proof { exp_mod_properties(); }
    if exp == 0 {
        1 % modulus
    } else {
        let half = mod_exp(base, exp / 2, modulus);
        let squared = mod_mult(half, half, modulus);
        if exp % 2 == 0 {
            squared
        } else {
            mod_mult(squared, base % modulus, modulus)
        }
    }
}

fn binary_to_int(s: &[char]) -> u64
    requires
        ValidBitString(s@),
        s@.len() <= 64,
    ensures
        binary_to_int(s) == Str2Int(s@),
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): No changes needed in code body */
    let x = binary_to_int(sx);
    let y = binary_to_int(sy);
    let z = binary_to_int(sz);
    
    let result_num = mod_exp(x % z, y, z);
    let result = int_to_binary(result_num);
    
    proof { exp_mod_properties(); }
    
    result
}
// </vc-code>

fn main() {}
}
