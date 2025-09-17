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
/* helper modified by LLM (iteration 10): fixed indexing to use usize instead of ranges */
exec fn str_to_int_exec(s: &[char]) -> (result: u64)
    ensures result == Str2Int(s@)
    decreases s.len()
{
    if s.is_empty() {
        0 as u64
    } else {
        let last_char = s[s.len() - 1];
        let last_bit: u64 = if last_char == '1' { 1 } else { 0 };
        let rest_slice: &[char] = if s.len() > 1 { &s[0..s.len() - 1] } else { &[] };
        let rest_value = str_to_int_exec(rest_slice);
        rest_value * (2 as u64) + last_bit
    }
}

/* helper modified by LLM (iteration 10): replaced nat with u64 in exec functions and adjusted specs */
exec fn int_to_str_exec(n: u64) -> (result: Vec<char>)
    ensures ValidBitString(result@) && Str2Int(result@) == n
    decreases n
{
    if n == (0 as u64) {
        vec!['0']
    } else if n == (1 as u64) {
        vec!['1']
    } else {
        let mut res = int_to_str_exec(n / 2);
        let last_digit = if n % 2 == (0 as u64) { '0' } else { '1' };
        res.push(last_digit);
        res
    }
}

/* helper modified by LLM (iteration 10): fixed indexing to use usize instead of ranges */
exec fn mod_exp_recursive(exponent: &[char], base: u64, modulus: u64) -> (result: u64)
    requires modulus > 1
    ensures result == Exp_int(base as nat, Str2Int(exponent@)) % (modulus as nat)
    decreases exponent.len()
{
    if exponent.is_empty() {
        1 as u64
    } else {
        let rest_slice: &[char] = if exponent.len() > 1 { &exponent[0..exponent.len() - 1] } else { &[] };
        let last_char = exponent[exponent.len() - 1];
        let t = mod_exp_recursive(rest_slice, base, modulus);
        let t2 = (t * t) % modulus;
        if last_char == '1' {
            (t2 * base) % modulus
        } else {
            t2
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): updated to use fixed helper functions with u64 */
{
    let x_int = str_to_int_exec(sx);
    let z_int = str_to_int_exec(sz);
    let result_int = mod_exp_recursive(sy, x_int, z_int);
    int_to_str_exec(result_int)
}
// </vc-code>

fn main() {}
}
