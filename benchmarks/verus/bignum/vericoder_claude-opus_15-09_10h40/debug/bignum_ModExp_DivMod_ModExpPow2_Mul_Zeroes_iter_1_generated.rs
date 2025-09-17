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
spec fn is_even(s: Seq<char>) -> bool
    recommends ValidBitString(s)
{
    s.len() == 0 || s.last() == '0'
}

spec fn div_by_2(s: Seq<char>) -> Seq<char>
    recommends ValidBitString(s), s.len() > 0
{
    s.subrange(0, s.len() - 1)
}

exec fn char_to_nat(c: char) -> (n: nat)
    requires c == '0' || c == '1'
    ensures n == if c == '1' { 1nat } else { 0nat }
{
    if c == '1' { 1 } else { 0 }
}

exec fn nat_to_bit_string(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
    decreases n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut res = nat_to_bit_string(n / 2);
        if n % 2 == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        res
    }
}

exec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 1
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half = mod_exp_helper(base, exp / 2, modulus);
        (half * half) % modulus
    } else {
        let rec = mod_exp_helper(base, exp - 1, modulus);
        (base * rec) % modulus
    }
}

exec fn str_to_nat(s: &[char]) -> (n: nat)
    requires ValidBitString(s@)
    ensures n == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = &s[0..s.len() - 1];
        let last_digit = if s[s.len() - 1] == '1' { 1 } else { 0 };
        2 * str_to_nat(prefix) + last_digit
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base_nat = str_to_nat(sx);
    let exp_nat = str_to_nat(sy);
    let mod_nat = str_to_nat(sz);
    let result_nat = mod_exp_helper(base_nat, exp_nat, mod_nat);
    nat_to_bit_string(result_nat)
}
// </vc-code>

fn main() {}
}
