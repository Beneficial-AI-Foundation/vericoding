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
spec fn pow_mod_correct(x: nat, y: nat, z: nat) -> bool {
    z > 1 ==> Exp_int(x, y) % z < z
}

proof fn str2int_bounds(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Exp_int(2, s.len())
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        str2int_bounds(s.subrange(0, s.len() as int - 1));
    }
}

proof fn exp_int_positive(x: nat, y: nat)
    ensures Exp_int(x, y) >= 1
    decreases y
{
    if y == 0 {
    } else {
        exp_int_positive(x, (y - 1) as nat);
    }
}

proof fn mod_result_bounds(a: nat, b: nat)
    requires b > 1
    ensures a % b < b
{
}

exec fn char_to_nat(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
            (c == '0' ==> result == 0),
            (c == '1' ==> result == 1)
{
    if c == '1' { 1 } else { 0 }
}

exec fn nat_mod_exp(base: nat, exp: nat, modulus: nat) -> (result: nat)
    requires modulus > 1
    ensures result == Exp_int(base, exp) % modulus,
            result < modulus
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else {
        let half_exp = exp / 2;
        let half_result = nat_mod_exp(base, half_exp, modulus);
        let squared = (half_result * half_result) % modulus;
        if exp % 2 == 1 {
            (squared * (base % modulus)) % modulus
        } else {
            squared
        }
    }
}

exec fn seq_to_nat(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = seq_to_nat(&s[..s.len()-1]);
        let last_digit = char_to_nat(s[s.len()-1]);
        2 * prefix + last_digit
    }
}

exec fn nat_to_binary_vec(mut n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
            Str2Int(result@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        let mut digits = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(digits@)
        {
            if temp % 2 == 1 {
                digits.push('1');
            } else {
                digits.push('0');
            }
            temp = temp / 2;
        }
        digits.reverse();
        digits
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    proof {
        str2int_bounds(sx@);
        str2int_bounds(sy@);
        str2int_bounds(sz@);
        exp_int_positive(Str2Int(sx@), Str2Int(sy@));
        mod_result_bounds(Exp_int(Str2Int(sx@), Str2Int(sy@)), Str2Int(sz@));
    }
    
    let x_val = seq_to_nat(sx);
    let y_val = seq_to_nat(sy);
    let z_val = seq_to_nat(sz);
    
    let result_val = nat_mod_exp(x_val, y_val, z_val);
    let result_vec = nat_to_binary_vec(result_val);
    
    result_vec
}
// </vc-code>

fn main() {}
}
