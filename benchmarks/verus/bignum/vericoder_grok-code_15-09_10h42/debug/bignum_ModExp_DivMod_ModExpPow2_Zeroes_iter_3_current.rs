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
/* helper modified by LLM (iteration 3): Changed all exec function types from nat to u64 and updated literals from nat to u64 to fix compilation errors */
exec fn str_to_nat(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@)
    ensures
        res as nat == Str2Int(s@)
    decreases
        s.len()
{
    if s.len() == 0u64 {
        return 0u64;
    } else {
        let recursive = str_to_nat(&s[0..(s.len() - 1 as usize)]);
        let char_val = if s[s.len() - 1] == '1' { 1u64 } else { 0u64 };
        return 2u64 * recursive + char_val;
    }
}

exec fn pow_mod(base: u64, exp: u64, module: u64) -> (res: u64)
    requires
        module > 0u64
    ensures
        res as nat == Exp_int(base as nat, exp as nat) % module as nat
    decreases
        exp
{
    if exp == 0u64 {
        return 1u64 % module;
    } else if exp % 2u64 == 0u64 {
        return pow_mod((base * base) % module, exp / 2u64, module);
    } else {
        let half_exp = (exp - 1u64) / 2u64;
        let square = pow_mod((base * base) % module, half_exp, module);
        let base_mod = base % module;
        return (square * base_mod) % module;
    }
}

exec fn nat_to_vec(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat
{
    let mut digs = Vec::new();
    let mut m = n;
    if m == 0u64 {
        digs.push('0');
    } else {
        while m > 0u64
            invariant
                true
            decreases
                m
        {
            digs.push(if m % 2u64 == 1u64 { '1' } else { '0' });
            m = m / 2u64;
        }
        digs.reverse();
    }
    digs
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Updated calls to use u64 types and adjusted for helper function changes */
{
    let x = str_to_nat(sx);
    let y = str_to_nat(sy);
    let z = str_to_nat(sz);
    let res_num = pow_mod(x, y, z);
    return nat_to_vec(res_num);
}
// </vc-code>

fn main() {}
}
