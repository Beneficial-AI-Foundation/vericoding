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
/* helper modified by LLM (iteration 4): changed to use u64 instead of nat */
exec fn str_to_int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    ensures res as nat == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        0u64
    } else {
        let last = s[s.len()-1];
        let rest = &s[0..s.len()-1];
        let rest_val = str_to_int_exec(rest);
        2u64 * rest_val + (if last == '1' { 1u64 } else { 0u64 })
    }
}

/* helper modified by LLM (iteration 4): changed to use u64 instead of nat */
exec fn int_to_str_exec(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == n as nat
{
    if n == 0u64 {
        vec!['0']
    } else {
        let last_bit = if n % 2u64 == 1u64 { '1' } else { '0' };
        let rest = int_to_str_exec(n / 2u64);
        let mut res_vec = rest;
        res_vec.push(last_bit);
        res_vec
    }
}

/* helper modified by LLM (iteration 4): changed to use u64 instead of nat */
exec fn mod_exp_right_to_left(base: u64, exponent: &[char], modulus: u64) -> (res: u64)
    requires modulus > 1
    ensures res as nat == Exp_int(base as nat, Str2Int(exponent@)) % (modulus as nat)
    decreases exponent.len()
{
    if exponent.len() == 0 {
        1u64
    } else {
        let last_bit = exponent[exponent.len()-1];
        let rest = &exponent[0..exponent.len()-1];
        let temp = mod_exp_right_to_left(base, rest, modulus);
        let temp_squared = (temp * temp) % modulus;
        if last_bit == '1' {
            (temp_squared * base) % modulus
        } else {
            temp_squared
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): changed helpers to use u64 instead of nat */
{
    let x = str_to_int_exec(sx);
    let z = str_to_int_exec(sz);
    let base_reduced = x % z;
    let result_int = mod_exp_right_to_left(base_reduced, sy, z);
    let result_str = int_to_str_exec(result_int);
    result_str
}
// </vc-code>

fn main() {}
}
