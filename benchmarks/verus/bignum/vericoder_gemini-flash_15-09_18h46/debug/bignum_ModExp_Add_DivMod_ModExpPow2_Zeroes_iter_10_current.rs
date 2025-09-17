use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed `u128::MAX` cap and directly used `pow` to fix previous compilation errors and ensure the direct translation of the spec to the exec code for `2^exponent` semantics, resolving the unresolved `pow` symbol from `vstd::arithmetic::power::pow`. */
use vstd::arithmetic::power::pow;

fn power_of_2_exec(exponent: usize) -> (result: u128)
  ensures result == pow(2, exponent as nat) as u128
{
  pow(2, exponent as nat) as u128
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed the `power_of_2_val_concrete` calculation by calling `power_of_2_exec` with `c_int as usize`. Also refined the modulo handling for `c_int = 0` to preserve the correct mathematical outcome. */
{
    let a_seq = a@;
    let b_seq = b@;

    let val_a = Str2Int(a_seq);
    let val_b = Str2Int(b_seq);

    let c_int: usize = a_seq.len();
    
    let mut val_mod_exec: u128 = 0;
    let power_of_2_val_concrete: u128 = power_of_2_exec(c_int as usize);
    
    let val_sum_u128: u128 = (val_a as u128).checked_add(val_b as u128).unwrap_or(u128::MAX);

    if c_int > 0 {
        val_mod_exec = val_sum_u128 % power_of_2_val_concrete;
    } else { // c_int == 0, equivalent to modulo by 2^0 = 1
        val_mod_exec = val_sum_u128 % 1; // Any number % 1 is 0
    }

    let mut bit_vec = Vec::<char>::new();
    let mut concrete_temp_val: u128 = val_mod_exec;

    let c_int_usize: usize = c_int;

    if c_int_usize == 0 && val_mod_exec == 0 { // special case a_seq.len() == 0 and result is 0
        bit_vec.push('0');
    } else {
        if concrete_temp_val == 0 {
             // If val_mod_exec is 0 but c_int_usize > 0, we still need to add c_int_usize zeroes
        } else {
            while concrete_temp_val > 0
                invariant
                    concrete_temp_val >= 0,
                    bit_vec.len() >= 0,
                decreases concrete_temp_val
            {
                if concrete_temp_val % 2 == 1 {
                    bit_vec.push('1');
                } else {
                    bit_vec.push('0');
                }
                concrete_temp_val = concrete_temp_val / 2;
            }
        }
    }

    let mut bit_vec_len_concrete: usize = bit_vec.len();

    while bit_vec_len_concrete < c_int_usize
        invariant
            bit_vec_len_concrete <= c_int_usize,
            bit_vec.len() == bit_vec_len_concrete,
            c_int_usize >= 0,
        decreases c_int_usize - bit_vec_len_concrete
    {
        bit_vec.push('0');
        bit_vec_len_concrete = bit_vec_len_concrete + 1;
    }

    if bit_vec.is_empty() && c_int_usize == 0 {
        bit_vec.push('0');
    }

    let mut reversed_bit_vec = Vec::<char>::new();
    
    // Reverse bit_vec in place for efficiency
    let mut i: isize = bit_vec.len() as isize - 1;
    while i >= 0
        invariant
            i >= -1,
            (bit_vec.len() as isize - 1 - i) <= bit_vec.len() as isize,
            bit_vec.len() <= c_int_usize + 1 || bit_vec.len() <= val_mod_exec.size_in_bits() as usize + 1,
        decreases i
    {
        reversed_bit_vec.push(bit_vec[i as usize]);
        i = i - 1;
    }

    // The above loop fills `reversed_bit_vec` from left to right with the bits in reverse order.
    // Then we reverse `reversed_bit_vec` to get it in the correct order.
    let mut final_result = Vec::<char>::new();
    let mut j: isize = reversed_bit_vec.len() as isize - 1;
    while j >= 0
        invariant
            j >= -1,
            final_result.len() as isize + j + 1 == reversed_bit_vec.len() as isize,
            final_result.len() as isize <= reversed_bit_vec.len() as isize,
        decreases j
    {
        let c = reversed_bit_vec.pop().unwrap(); // Use pop for exec code
        final_result.insert(0, c); // Insert at beginning to reverse
        j = j - 1;
    }
    final_result
}
// </vc-code>

fn main() {}
}

