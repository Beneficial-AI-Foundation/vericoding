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
/* helper modified by LLM (iteration 2): Fixed nat type usage and added proper spec functions */
exec fn modular_exp(base: u64, exp: u64, modulus: u64) -> (result: u64)
    requires modulus > 1
    ensures result == Exp_int(base as nat, exp as nat) % modulus as nat
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half_exp = modular_exp(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * modular_exp(base, exp - 1, modulus)) % modulus
    }
}

exec fn nat_to_binary_vec(mut n: u64) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        proof {
            assert(ValidBitString(result@));
        }
        result
    } else {
        let mut result = Vec::new();
        while n > 0
            invariant ValidBitString(result@)
        {
            if n % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            n = n / 2;
            proof {
                assert(ValidBitString(result@));
            }
        }
        result.reverse();
        proof {
            assert(ValidBitString(result@));
        }
        result
    }
}

spec fn u64_to_nat(x: u64) -> nat { x as nat }

proof fn str2int_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) <= u64::MAX as nat
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed nat type usage and variable scoping */
    proof {
        str2int_bound(sx@);
        str2int_bound(sy@);
        str2int_bound(sz@);
    }
    
    let base = Str2Int(sx@) as u64;
    let exp = Str2Int(sy@) as u64;
    let modulus = Str2Int(sz@) as u64;
    
    let result_nat = modular_exp(base, exp, modulus);
    let result_vec = nat_to_binary_vec(result_nat);
    
    proof {
        assert(ValidBitString(result_vec@));
        assert(Str2Int(result_vec@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    result_vec
}
// </vc-code>

fn main() {}
}
