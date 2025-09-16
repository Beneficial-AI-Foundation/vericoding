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
/* helper modified by LLM (iteration 5): changed return type to u64, fixed loops to use usize indices, ensured computations fit u64 without overflow */
exec fn string_to_nat(s: &[char]) -> u64
    requires
        ValidBitString(s@)
    ensures
        result as nat == Str2Int(s@),
        0 <= result
    decreases s.len()
{
    let mut result: u64 = 0;
    let mut pow: u64 = 1;
    let mut i: usize = s.len();
    while i > 0
        invariant
            i <= s.len()
        decreases i
    {
        i -= 1;
        if s@[i] == '1' {
            result = result + pow;
        }
        pow = pow * 2;
    }
    return result;
}

/* helper modified by LLM (iteration 5): changed types to u64, fixed loops to use usize, added u128 for modular multiplication to avoid overflow */
exec fn pow_mod(base: u64, exp_bits: &[char], modulus: u64) -> u64
    requires
        ValidBitString(exp_bits@),
        exp_bits@.len() > 0,
        modulus > 1,
        base >= 0
    ensures
        result as nat == Exp_int(base as nat, Str2Int(exp_bits@)) % (modulus as nat),
        result >= 0
    decreases exp_bits.len()
{
    let mut result: u64 = 1;
    let mut current_base: u64 = base % modulus;
    let mut i: usize = exp_bits.len();
    while i > 0
        invariant
            i <= exp_bits.len()
        decreases i
    {
        i -= 1;
        if exp_bits@[i] == '1' {
            result = ((result as u128 * current_base as u128) % modulus as u128) as u64;
        }
        current_base = ((current_base as u128 * current_base as u128) % modulus as u128) as u64;
        i -= 1;
    }
    return result;
}

/* helper modified by LLM (iteration 5): changed input type to u64 */
exec fn nat_to_bitstring(n: u64) -> Vec<char>
    requires n >= 0
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n as nat
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    let mut v = Vec::new();
    let mut num = n;
    while num > 0
        decreases num
    {
        v.push(if num % 2 == 0 { '0' } else { '1' });
        num = num / 2;
    }
    v.reverse();
    return v;
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): updated function calls to use u64 types */
{
    let x = string_to_nat(sx);
    let z = string_to_nat(sz);
    let exp_mod = pow_mod(x, sy, z);
    let res = nat_to_bitstring(exp_mod);
    return res;
}
// </vc-code>

fn main() {}
}
