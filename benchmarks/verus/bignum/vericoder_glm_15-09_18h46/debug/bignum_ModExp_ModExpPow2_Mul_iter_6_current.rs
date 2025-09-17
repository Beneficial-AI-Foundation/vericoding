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
/* helper modified by LLM (iteration 6): fixed int/usize type errors and seq_repeat usage */
exec fn add_bit_strings(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(a@) + Str2Int(b@)
{
    let max_len = std::cmp::max(a.len(), b.len());
    let mut result = Vec::new();
    let mut carry = false;

    for i in 0..max_len {
        let bit_a = if i < a.len() { a[a.len() - 1 - i] } else { '0' };
        let bit_b = if i < b.len() { b[b.len() - 1 - i] } else { '0' };

        let sum_val = (bit_a == '1') as u32 + (bit_b == '1') as u32 + (if carry { 1 } else { 0 });
        let new_bit = if sum_val % 2 == 1 { '1' } else { '0' };
        carry = sum_val >= 2;
        result.push(new_bit);
    }

    if carry {
        result.push('1');
    }

    result.reverse();
    result
}

/* helper modified by LLM (iteration 6): no changes needed */
exec fn shift_left(a: &[char], shift: usize) -> (res: Vec<char>)
    requires ValidBitString(a@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(a@) * (2 as nat).pow(shift as nat)
{
    let mut res = a.to_vec();
    for _ in 0..shift {
        res.push('0');
    }
    res
}

/* helper modified by LLM (iteration 6): no changes needed */
exec fn multiply_bit_strings(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(a@) * Str2Int(b@)
{
    let mut result = vec!['0'];
    for j in 0..b.len() {
        if b[b.len()-1-j] == '1' {
            let shifted = shift_left(a, j);
            result = add_bit_strings(&result, &shifted);
        }
    }
    result
}

/* helper modified by LLM (iteration 6): replaced seq_repeat with explicit condition */
exec fn reduce_power_of_two(a: &[char], modulus: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(modulus@),
             exists |k: nat| 
                 modulus@.len() == k + 1 &&
                 modulus@[0] == '1' &&
                 (forall |i: int| 1 <= i < k + 1 ==> modulus@[i] == '0')
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(a@) % Str2Int(modulus@)
{
    let k = modulus.len() - 1;
    if a.len() < k {
        let mut padded = vec!['0'; k - a.len()];
        padded.extend(a);
        padded
    } else {
        a[a.len()-k..].to_vec()
    }
}

/* helper modified by LLM (iteration 6): replaced seq_repeat with explicit condition */
exec fn mul_mod(a: &[char], b: &[char], modulus: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@), ValidBitString(modulus@),
             exists |k: nat| 
                 modulus@.len() == k + 1 &&
                 modulus@[0] == '1' &&
                 (forall |i: int| 1 <= i < k + 1 ==> modulus@[i] == '0')
    ensures ValidBitString(res@), Str2Int(res@) == (Str2Int(a@) * Str2Int(b@)) % Str2Int(modulus@)
{
    let product = multiply_bit_strings(a, b);
    reduce_power_of_two(&product, modulus)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented ModExp algorithm for power-of-two modulus */
{
    if sy.len() == 1 {
        if sy[0] == '1' {
            reduce_power_of_two(sx, sz)
        } else {
            vec!['1']
        }
    } else {
        let last_bit = sy[sy.len()-1];
        let rest_exp = &sy[0..sy.len()-1];
        let temp_result = ModExp_ModExpPow2_Mul(sx, rest_exp, sz);
        let squared = mul_mod(&temp_result, &temp_result, sz);
        let base_mod = reduce_power_of_two(sx, sz);
        let result = if last_bit == '1' {
            mul_mod(&squared, &base_mod, sz)
        } else {
            squared
        };
        result
    }
}
// </vc-code>

fn main() {}
}
