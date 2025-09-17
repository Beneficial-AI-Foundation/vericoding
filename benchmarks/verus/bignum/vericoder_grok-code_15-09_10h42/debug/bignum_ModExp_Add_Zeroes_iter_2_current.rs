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
/* helper modified by LLM (iteration 2): Added helper function to convert string to nat with fixed syntax */
exec fn str_to_nat(s: Seq<char>) -> nat
    requires
        ValidBitString(s),
    ensures
        str_to_nat(s) == Str2Int(s),
    decreases
        s.len(),
{
    if s.len() == 0 { 0 } else { 2 * str_to_nat(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }) }
}

/* helper modified by LLM (iteration 2): Added helper function to compute modular exponentiation */
exec fn mod_pow(base: nat, exp: nat, modulus: nat) -> nat
    requires
        modulus > 1,
    ensures
        mod_pow(base, exp, modulus) == Exp_int(base, exp) % modulus,
{
    let mut result = 1;
    let mut b = base % modulus;
    let mut e = exp;
    while e > 0
        invariant
            e >= 0,
        decreases
            e,
    {
        if e % 2 == 1 {
            result = (result * b) % modulus;
        }
        b = (b * b) % modulus;
        e = e / 2;
    }
    result
}

/* helper modified by LLM (iteration 2): Added helper function to convert nat to binary string */
exec fn nat_to_binary(n: nat) -> Vec<char>
    ensures
        ValidBitString(nat_to_binary(n)@),
        Str2Int(nat_to_binary(n)@) == n,
{
    if n == 0 {
        vec!['0']
    } else {
        let mut v = Vec::new();
        let mut nn = n;
        while nn > 0
            invariant
                nn >= 0,
            decreases
                nn,
        {
            v.push(if nn % 2 == 1 { '1' } else { '0' });
            nn = nn / 2;
        }
        v.reverse();
        v
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
/* code modified by LLM (iteration 2): Implemented modular exponentiation using helper functions */
{
    let x = str_to_nat(sx@);
    let y = str_to_nat(sy@);
    let z = str_to_nat(sz@);
    let res_nat = mod_pow(x, y, z);
    let res = nat_to_binary(res_nat);
    res
}
// </vc-code>

fn main() {}
}
