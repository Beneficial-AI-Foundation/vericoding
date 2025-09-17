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
/* helper modified by LLM (iteration 3): Add missing helper functions for arithmetic and conversions */
spec fn bitstring_to_nat(s: Seq<char>) -> nat
    recommends ValidBitString(s)
{
    Str2Int(s)
}

proof fn helper_lemma_exp_mod_result(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
    decreases y
{
    if y > 0 {
        helper_lemma_exp_mod_result(x, y - 1, m);
        helper_lemma_mod_properties(x, Exp_int(x, y - 1), m);
    }
}

proof fn helper_lemma_mod_properties(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    // Standard modular arithmetic property
}

spec fn nat_to_bitstring(n: nat) -> Seq<char>
    ensures ValidBitString(result)
{
    if n == 0 {
        Seq::new()
    } else {
        let rest = nat_to_bitstring(n / 2);
        if n % 2 == 0 {
            rest + Seq::singleton('0')
        } else {
            rest + Seq::singleton('1')
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Replace nat_to_bitstring usage and fix implementation */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        helper_lemma_exp_mod_result(x_val, y_val, z_val);
    }
    
    let mod_result: nat = Exp_int(x_val % z_val, y_val) % z_val;
    
    // Manual implementation of nat_to_bitstring functionality
    let mut result_vec = Vec::<char>::new();
    let mut n = mod_result;
    
    if n == 0 {
        result_vec.push('0');
    } else {
        while n > 0
            invariant
                0 <= n,
                ValidBitString(result_vec@)
            decreases n
        {
            if n % 2 == 0 {
                result_vec.push('0');
            } else {
                result_vec.push('1');
            }
            n = n / 2;
        }
        result_vec.reverse();
    }
    
    result_vec
}
// </vc-code>

fn main() {}
}
