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
/* helper modified by LLM (iteration 2): Changed helper function `power_mod` to return `nat` type to avoid conflicts with ghost code variable types. The modulo operator is still `nat` compatible. */
spec fn power_mod(base: nat, exp: nat, modulus: nat) -> nat
decreases exp
{
    if modulus == 0 { 0 } else if exp == 0 { 1 % modulus } else {
        let half_exp = power_mod(base, (exp / 2) as nat, modulus);
        let half_exp_sq = (half_exp * half_exp) % modulus;
        if exp % 2 == 0 { half_exp_sq } else { (base * half_exp_sq) % modulus }
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
/* code modified by LLM (iteration 2): Refactored nat_to_bit_seq conversion and handling of bit string output. Changed `nat` to `u128` for executable code and type casting. The `Str2Int` and `power_mod` still use `nat` in their ghost definitions. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = power_mod(x_int, y_int, z_int);

    let mut bits: Seq<char> = Seq::empty();
    let mut temp: u128 = result_nat as u128;
    if temp == 0 {
        bits = bits.push('0');
    }
    while temp > 0
        invariant
             temp >= 0,
             bits.len() >= 0,
        decreases temp
    {
        if temp % 2 == 1 { bits = bits.push('1'); } else { bits = bits.push('0'); }
        temp = temp / 2;
    }
    
    let reversed_bits = bits.rev();
    
    let mut res_vec = Vec::<char>::new();
    let mut i: u64 = 0;
    while (i as int) < reversed_bits.len()
        invariant
            0 <= i as int <= reversed_bits.len(),
            res_vec.len() == i as nat,
            forall |j: int| 0 <= j < i as int ==> res_vec.index(j) == reversed_bits.index(j),
        decreases reversed_bits.len() - (i as int)
    {
        res_vec.push(reversed_bits.index(i as int));
        i = i + 1;
    }

    res_vec
}
// </vc-code>

fn main() {}
}
