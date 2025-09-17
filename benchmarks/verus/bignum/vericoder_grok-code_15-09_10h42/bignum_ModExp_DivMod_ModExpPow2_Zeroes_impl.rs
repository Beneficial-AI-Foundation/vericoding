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
exec fn str_to_nat(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@)
    ensures
        res as nat == Str2Int(s@)
    decreases s.len()
{
    let mut res = 0u64;
    let mut i = 0usize;
    while i < s.len()
        invariant
            0 <= i as int <= s.len() as int,
            res as nat == Str2Int(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        let bit = if s[i] == '1' { 1u64 } else { 0u64 };
        res = 2u64 * res + bit;
        i += 1;
    }
    res
}

exec fn pow_mod(base: u64, exp: u64, module: u64) -> (res: u64)
    requires
        module > 0u64
    ensures
        res as nat == Exp_int(base as nat, exp as nat) % module as nat
    decreases exp
{
    if exp == 0u64 {
        return 1u64 % module;
    } else if exp % 2u64 == 0u64 {
        let bb = (((base as u128 * base as u128) % module as u128)) as u64;
        return pow_mod(bb, exp / 2u64, module);
    } else {
        let half_exp = (exp - 1u64) / 2u64;
        let bb = (((base as u128 * base as u128) % module as u128)) as u64;
        let square = pow_mod(bb, half_exp, module);
        let base_mod = ((base as u128 % module as u128)) as u64;
        return (((square as u128 * base_mod as u128) % module as u128)) as u64;
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
                Str2Int(digs@) == (n as nat / Exp_int(2, digs.len() as nat)) as nat % (m as nat + 1),
            decreases m
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
/* code modified by LLM (iteration 5): implementation calls fixed helpers with iterative str_to_nat and overflow-safe pow_mod */
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
