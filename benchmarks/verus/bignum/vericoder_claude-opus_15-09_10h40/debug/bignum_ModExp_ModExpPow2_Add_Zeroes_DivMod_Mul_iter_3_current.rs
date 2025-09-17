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
/* helper modified by LLM (iteration 3): Fixed slice indexing to use usize */
proof fn exp_mod_lemma(x: nat, y: nat, z: nat)
    requires
        z > 1
    ensures
        Exp_int(x, y) % z == if y == 0 { 1nat % z } else { (x * Exp_int(x, (y - 1) as nat)) % z }
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

proof fn mod_mul_lemma(a: nat, b: nat, m: nat)
    requires
        m > 0
    ensures
        (a * b) % m == ((a % m) * (b % m)) % m
{
}

exec fn str_to_int_exec(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 63
    ensures
        res == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        return 0;
    } else {
        let len_minus_one: usize = (s.len() - 1) as usize;
        let prev = str_to_int_exec(&s[..len_minus_one]);
        let last_bit = if s[s.len() - 1] == '1' { 1u64 } else { 0u64 };
        return 2 * prev + last_bit;
    }
}

exec fn int_to_str_exec(mut n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
    decreases n
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    while n > 0
        invariant
            ValidBitString(result@)
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    result.reverse();
    return result;
}

exec fn mod_exp_helper(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires
        modulus > 1,
        base < modulus
    ensures
        res == Exp_int(base as nat, exp as nat) % (modulus as nat),
        res < modulus
    decreases exp
{
    if exp == 0 {
        return 1;
    } else {
        let half_exp = exp / 2;
        let half_result = mod_exp_helper(base, half_exp, modulus);
        let squared = ((half_result as u128 * half_result as u128) % (modulus as u128)) as u64;
        if exp % 2 == 0 {
            return squared;
        } else {
            return ((squared as u128 * base as u128) % (modulus as u128)) as u64;
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Implementation unchanged */
    let x_int = str_to_int_exec(sx);
    let y_int = str_to_int_exec(sy);
    let z_int = str_to_int_exec(sz);
    
    let result_int = mod_exp_helper(x_int % z_int, y_int, z_int);
    
    let result = int_to_str_exec(result_int);
    return result;
}
// </vc-code>

fn main() {}
}
