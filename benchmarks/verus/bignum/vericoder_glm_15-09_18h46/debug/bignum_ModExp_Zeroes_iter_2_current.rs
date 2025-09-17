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
/* helper modified by LLM (iteration 2): fixed invariant blocks to use comma-separated list */
spec fn bits_to_nat_reversed(bits: Seq<char>) -> nat
    decreases bits.len()
{
    if bits.len() == 0 { 0 }
    else { (if bits.index(0) == '1' { 1 } else { 0 }) + 2 * bits_to_nat_reversed(bits.subrange(1, bits.len() as int)) }
}
exec fn str2int(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut n: nat = 0;
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            n == Str2Int(s@.subrange(0, i as int))
    {
        let bit = s[i];
        let digit = if bit == '1' { 1 } else { 0 };
        n = n * 2 + digit;
    }
    n
}
exec fn int2str(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut bits = Vec::new();
        let mut current = n;
        while current > 0
            invariant
                current >= 0,
                n == current * (2 as nat).pow(bits.len() as nat) + bits_to_nat_reversed(bits@)
        {
            let bit = if current % 2 == 1 { '1' } else { '0' };
            bits.push(bit);
            current = current / 2;
        }
        bits.reverse();
        bits
    }
}
exec fn mod_exp(base: nat, exponent: &[char], modulus: nat) -> (res: nat)
    requires ValidBitString(exponent@) && modulus > 1
    ensures res == Exp_int(base, Str2Int(exponent@)) % modulus
{
    if exponent.len() == 0 {
        1 % modulus
    } else {
        let mut result = 1;
        let mut base = base % modulus;
        for i in 0..exponent.len()
            invariant
                0 <= i <= exponent.len(),
                result == Exp_int(base, Str2Int(exponent@.subrange(0, i as int))) % modulus
        {
            result = (result * result) % modulus;
            if exponent[i] == '1' {
                result = (result * base) % modulus;
            }
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): no changes needed */
    let base = str2int(sx);
    let modulus_val = str2int(sz);
    let result_nat = mod_exp(base, sy, modulus_val);
    let result_vec = int2str(result_nat);
    result_vec
}
// </vc-code>

fn main() {}
}
