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
exec fn str_to_int_exec(s: Seq<char>) -> (result: nat)
    requires ValidBitString(s)
    ensures result == Str2Int(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_char = s.index(s.len() - 1);
        let last_bit = if last_char == '1' { 1 } else { 0 };
        let rest = s.subrange(0, s.len() - 1);
        2 * str_to_int_exec(rest) + last_bit
    }
}

exec fn int_to_str_exec(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@) && Str2Int(result@) == n
    decreases n
{
    if n == 0 {
        vec!['0']
    } else if n == 1 {
        vec!['1']
    } else {
        let mut res = int_to_str_exec(n / 2);
        let last_digit = if n % 2 == 0 { '0' } else { '1' };
        res.push(last_digit);
        res
    }
}

exec fn mod_exp_recursive(exponent: Seq<char>, base: nat, modulus: nat) -> (result: nat)
    requires ValidBitString(exponent), modulus > 1
    ensures result == Exp_int(base, Str2Int(exponent)) % modulus
    decreases exponent.len()
{
    if exponent.len() == 0 {
        1
    } else {
        let rest = exponent.subrange(0, exponent.len() - 1);
        let last_char = exponent.index(exponent.len() - 1);
        let t = mod_exp_recursive(rest, base, modulus);
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
{
    let x_int = str_to_int_exec(sx@);
    let z_int = str_to_int_exec(sz@);
    let result_int = mod_exp_recursive(sy@, x_int, z_int);
    int_to_str_exec(result_int)
}
// </vc-code>

fn main() {}
}
