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
/* helper modified by LLM (iteration 5): Fixed slice indexing to use usize */
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

exec fn char_to_nat(c: char) -> (n: u64)
    requires c == '0' || c == '1'
    ensures n == if c == '1' { 1u64 } else { 0u64 }
{
    if c == '1' { 1u64 } else { 0u64 }
}

exec fn nat_to_bit_string(n: u64) -> (res: Vec<char>)
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

exec fn mod_exp_helper(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1
    ensures res == Exp_int(base as nat, exp as nat) % (modulus as nat)
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

exec fn str_to_nat(s: &[char]) -> (n: u64)
    requires ValidBitString(s@)
    ensures n == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0
    } else {
        let mut acc: u64 = 0;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                acc == Str2Int(s@.subrange(0, i as int))
        {
            let digit = if s[i] == '1' { 1u64 } else { 0u64 };
            acc = acc * 2 + digit;
            i = i + 1;
        }
        acc
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
    /* code modified by LLM (iteration 5): Use u64 types in exec context */
    let base_nat = str_to_nat(sx);
    let exp_nat = str_to_nat(sy);
    let mod_nat = str_to_nat(sz);
    let result_nat = mod_exp_helper(base_nat, exp_nat, mod_nat);
    nat_to_bit_string(result_nat)
}
// </vc-code>

fn main() {}
}
