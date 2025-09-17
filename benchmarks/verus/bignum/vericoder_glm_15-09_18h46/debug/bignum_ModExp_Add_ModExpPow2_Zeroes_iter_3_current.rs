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
/* helper modified by LLM (iteration 3): fixed nat literal syntax */
exec fn str_to_int_exec(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        0 as nat
    } else {
        let last = s[s.len()-1];
        let rest = &s[0..s.len()-1];
        let rest_val = str_to_int_exec(rest);
        2 as nat * rest_val + (if last == '1' { 1 as nat } else { 0 as nat })
    }
}

/* helper modified by LLM (iteration 3): fixed nat literal syntax */
exec fn int_to_str_exec(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == n
{
    if n == 0 as nat {
        vec!['0']
    } else {
        let last_bit = if n % 2 == 1 as nat { '1' } else { '0' };
        let rest = int_to_str_exec(n / (2 as nat));
        let mut res = rest;
        res.push(last_bit);
        res
    }
}

/* helper modified by LLM (iteration 3): fixed nat literal syntax */
exec fn mod_exp_right_to_left(base: nat, exponent: &[char], modulus: nat) -> (res: nat)
    requires modulus > 1
    ensures res == Exp_int(base, Str2Int(exponent@)) % modulus
    decreases exponent.len()
{
    if exponent.len() == 0 {
        1 as nat
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
/* code modified by LLM (iteration 3): fixed helpers, no changes to main logic */
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
