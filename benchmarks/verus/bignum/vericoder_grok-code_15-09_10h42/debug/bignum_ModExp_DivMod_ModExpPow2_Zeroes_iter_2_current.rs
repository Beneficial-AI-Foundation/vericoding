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
/* helper modified by LLM (iteration 2): Fixed type mismatches by using nat literals for integer constants to match nat operations */
exec fn str_to_nat(s: &[char]) -> (res: nat)
    requires
        ValidBitString(s@)
    ensures
        res == Str2Int(s@)
    decreases
        s.len()
{
    if s.len() == 0nat {
        return 0nat;
    } else {
        let recursive = str_to_nat(&s[0..s.len()-1]);
        let char_val = if s[s.len()-1] == '1' { 1nat } else { 0nat };
        return 2nat * recursive + char_val;
    }
}

exec fn pow_mod(base: nat, exp: nat, module: nat) -> (res: nat)
    requires
        module > 0nat
    ensures
        res == Exp_int(base, exp) % module
    decreases
        exp
{
    if exp == 0nat {
        return 1nat % module;
    } else if exp % 2nat == 0nat {
        return pow_mod((base * base) % module, exp / 2nat, module);
    } else {
        let half_exp = (exp - 1nat) / 2nat;
        let square = pow_mod((base * base) % module, half_exp, module);
        let base_mod = base % module;
        return (square * base_mod) % module;
    }
}

exec fn nat_to_vec(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
{
    let mut digs = Vec::new();
    let mut m = n;
    if m == 0nat {
        digs.push('0');
    } else {
        while m > 0nat
            invariant
                true
            decreases
                m
        {
            digs.push(if m % 2nat == 1nat {'1'} else {'0'});
            m = m / 2nat;
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
/* code modified by LLM (iteration 2): Implemented the method body by calling helper functions to compute modular exponentiation */
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
