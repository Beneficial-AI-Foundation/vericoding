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
/* helper modified by LLM (iteration 4): Added parentheses around type casts in requires to fix compilation error */
spec fn str2nat_fits_in_u64(s: Seq<char>) -> bool
{
    Str2Int(s) < 18446744073709551616
}

/* helper modified by LLM (iteration 4): Added parentheses around type casts in requires; added exec str_to_u64 */
exec fn mod_pow(base: u64, exp: u64, modulus: u64) -> u64
    requires
        modulus > 1,
        (base as nat) < 18446744073709551616,
        (modulus as nat) < 18446744073709551616,
    ensures
        mod_pow(base, exp, modulus) as nat == Exp_int(base as nat, exp as nat) % modulus as nat,
    decreases exp,
{
    let mut result: u64 = 1;
    let mut b: u64 = ((base as i128 % modulus as i128) as u64);
    let mut e: u64 = exp;
    while e > 0
        invariant
            e >= 0,
        decreases e as nat,
    {
        if e % 2 == 1 {
            result = (((result as i128 * b as i128) % modulus as i128) as u64);
        }
        b = (((b as i128 * b as i128) % modulus as i128) as u64);
        e = e / 2;
    }
    result
}

/* helper modified by LLM (iteration 4): Added exec str_to_u64 */
exec fn str_to_u64(s: Seq<char>) -> u64
    requires
        ValidBitString(s),
        Str2Int(s) < 18446744073709551616,
    ensures
        Str2Int(s) == str_to_u64(s) as nat,
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        2 * str_to_u64(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 })
    }
}

/* helper modified by LLM (iteration 4): unchanged */
exec fn nat_to_binary(n: u64) -> Vec<char>
    ensures
        ValidBitString(nat_to_binary(n)@),
        Str2Int(nat_to_binary(n)@) == n as nat,
    decreases n,
{
    if n == 0 {
        vec!['0']
    } else {
        let mut v = Vec::new();
        let mut nn = n;
        while nn > 0
            invariant
                nn >= 0,
            decreases nn as nat,
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
/* code modified by LLM (iteration 4): Added call to str_to_u64 and assertion */
{
    spec fn all_fits_in_u64(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> bool
    {
        ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz) &&
        sy.len() > 0 && Str2Int(sz) > 1 &&
        Str2Int(sx) < 18446744073709551616 &&
        Str2Int(sy) < 18446744073709551616 &&
        Str2Int(sz) < 18446744073709551616
    }

    proof {
        assert(all_fits_in_u64(sx@, sy@, sz@));
    }
    let x = str_to_u64(sx@);
    let y = str_to_u64(sy@);
    let z = str_to_u64(sz@);
    let res_nat = mod_pow(x, y, z);
    let res = nat_to_binary(res_nat);
    res
}
// </vc-code>

fn main() {}
}
