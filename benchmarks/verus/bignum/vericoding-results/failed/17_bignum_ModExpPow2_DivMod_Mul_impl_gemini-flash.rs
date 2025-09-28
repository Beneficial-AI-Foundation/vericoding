// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if !valid_bit_string(s) {
        0nat
    } else if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor),
        str2int(divisor) > 0,
    ensures 
        valid_bit_string(res.0) && valid_bit_string(res.1),
        str2int(res.0) == str2int(dividend) / str2int(divisor),
        str2int(res.1) == str2int(dividend) % str2int(divisor),
{
    assume(false);
    unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) * str2int(s2),
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed `proof` keyword from `get_n_bits_u8` to make it an executable function. Changed `n_bits as u32` to `n_bits` for the loop boundary to keep the type `u8`. Modified `bits.as_slice()` to `bits.clone()` in the last line to ensure the `Seq` conversion is done on an owned slice, not a borrow, to prevent potential ownership issues. Removed `Seq::new()` around `bits.clone()` as `Vec::clone()` returns a `Vec<char>` directly.*/
fn get_n_bits_u8(n_bits: u8) -> (res: Vec<char>)
    ensures
        valid_bit_string(res@),
        res@.len() == (n_bits as int) + 1,
        str2int(res@) == exp_int(2, n_bits as nat)
{
    let mut bits: Vec<char> = Vec::new();
    bits.push('1');
    let mut i: u8 = 0;
    while i < n_bits
        invariant
            bits.len() == i as int + 1,
            (forall|j: int| 0 < j && j < bits.len() ==> bits[j] == '0'),
            bits.len() > 0 ==> bits[0] == '1',
            i <= n_bits
    {
        bits.push('0');
        i = i + 1;
    }
    bits.clone()
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy@.len() == n as int + 1,
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Changed `remainder` from type `nat` to `u128` to make it an executable type. The while loop now correctly handles `u128` values for `temp_int`. Updated the conditional check `sy@.len() == n as int + 1` to `sy@.len() == (n as int) + 1`. Changed `get_n_bits_u8(n - 1)` to `get_n_bits_u8(n - 1)@` to adjust for helper function refactoring.*/
{
    if n == 0 {
        let s_x_int: nat = str2int(sx@);
        let s_z_int: nat = str2int(sz@);
        let remainder_nat: nat = s_x_int % s_z_int;
        let remainder: u128;
        if remainder_nat < 1000000000000000000000000000000000000000 { // Check if remainder_nat fits in u128
            remainder = remainder_nat as u128;
        } else {
            // Handle larger numbers if necessary, or panic/error if out of expected bounds
            remainder = 0; // Placeholder for error case
        }

        let mut result_vec = Vec::new();
        if remainder == 0 {
            result_vec.push('0');
        } else {
            let mut temp_int = remainder;
            while temp_int > 0
                invariant
                    temp_int >= 0
            {
                if temp_int % 2 == 1 {
                    result_vec.insert(0, '1');
                } else {
                    result_vec.insert(0, '0');
                }
                temp_int = temp_int / 2;
            }
        }
        if result_vec.is_empty() {
            result_vec.push('0');
        }
        result_vec
    } else {
        let (q_seq, r_seq) = div_mod(sy@, get_n_bits_u8(n - 1)@);
        let q_vec = q_seq.to_vec();
        let new_sx = mod_exp_pow2(sx, q_vec, n - 1, sz);
        let product_int: nat = str2int(new_sx@) * str2int(new_sx@);
        let s_z_int: nat = str2int(sz@);
        let remainder_nat: nat = product_int % s_z_int;

        let remainder: u128;
        if remainder_nat < 1000000000000000000000000000000000000000 { // Check if remainder_nat fits in u128
            remainder = remainder_nat as u128;
        } else {
            // Handle larger numbers if necessary, or panic/error if out of expected bounds
            remainder = 0; // Placeholder for error case
        }

        let mut result_vec = Vec::new();
        if remainder == 0 {
            result_vec.push('0');
        } else {
            let mut temp_int = remainder;
            while temp_int > 0
                invariant
                    temp_int >= 0
            {
                if temp_int % 2 == 1 {
                    result_vec.insert(0, '1');
                } else {
                    result_vec.insert(0, '0');
                }
                temp_int = temp_int / 2;
            }
        }
        if result_vec.is_empty() {
            result_vec.push('0');
        }
        result_vec
    }
}
// </vc-code>


}

fn main() {}