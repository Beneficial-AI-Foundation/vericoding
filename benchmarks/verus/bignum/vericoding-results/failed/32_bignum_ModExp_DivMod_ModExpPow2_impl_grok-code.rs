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
/* helper modified by LLM (iteration 9): added invariants and decreases clauses to while loops in Int2Str for verification */exec fn Int2Str(x: u64) -> Vec<char>
{
    if x == 0u64 {
        return vec!['0'];
    }
    let mut num_bits = 0u64;
    let mut temp = x;
    while temp > 0u64
        invariant temp >= 0
        decreases temp
    {
        num_bits += 1u64;
        temp /= 2u64;
    }
    // now num_bits is the number of bits
    let mut res = Vec::new();
    let mut i = num_bits;
    while i > 0
        invariant i >= 0, i <= num_bits
        decreases i
    {
        i -= 1;
        let bit = (x >> i) & 1u64;
        res.push(if bit == 1u64 { '1' } else { '0' });
    }
    res
}

exec fn bin_to_int(s: &[char]) -> u64
{
    let mut result: u64 = 0u64;
    let mut i = 0;
    while i < s.len()
        invariant i <= s.len(), 0 <= i <= s@.len()
        decreases s@.len() - i
    {
        result = result * 2u64 + if s[i] == '1' { 1u64 } else { 0u64 };
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 9): added invariant and decreases to loop in pow_mod for verification */exec fn pow_mod(base: u64, exp: &[char], modulus: u64) -> u64
{
    if exp.len() == 0 {
        1u64
    } else {
        let mut result: u64 = 1u64;
        let mut base_pow: u64 = base % modulus;
        let mut i: usize = exp.len() - 1;
        loop
            invariant i <= exp.len() - 1, i >= 0
            decreases i
        {
            if exp[i] == '1' {
                result = ((((result as u128) * (base_pow as u128)) % (modulus as u128)) as u64);
            }
            base_pow = ((((base_pow as u128) * (base_pow as u128)) % (modulus as u128)) as u64);
            if i == 0 {
                break;
            }
            i -= 1;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): implemented with helper functions */{
    let base_int = bin_to_int(sx);
    let modulus = bin_to_int(sz);
    let res_int = pow_mod(base_int, sy, modulus);
    Int2Str(res_int)
}
// </vc-code>

fn main() {}
}
