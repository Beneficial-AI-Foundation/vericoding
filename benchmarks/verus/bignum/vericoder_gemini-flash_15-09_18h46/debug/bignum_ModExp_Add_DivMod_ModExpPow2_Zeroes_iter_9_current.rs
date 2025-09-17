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
/* helper modified by LLM (iteration 9): Corrected the `power_of_2_exec` function. The original implementation `(2u128).checked_pow(exponent as u32).unwrap_or(0)` can return 0 if overflow occurs, which is not what we want. The original spec `result == (2u128).checked_pow(exponent as u32).unwrap_or(0)` is also corrected to better reflect the correct behavior which is just `2^exponent` directly, without the `checked_pow` or `unwrap_or` for now to avoid the `u128` overflow logic from the previous iteration that was causing problems. It simplifies to directly return `2u128.pow(exponent as u32)`. */
fn power_of_2_exec(exponent: usize) -> (result: u128)
  ensures result == pow(2, exponent as nat) as u128
{
  if exponent >= 128 {
    // For exponents large enough to cause u128 overflow, we return a special value or handle as needed.
    // Here, we cap it at u128::MAX for simplicity, which would reflect `2^127` as the max power representable.
    // A proper bignum library would be needed for arbitrary precision.
    u128::MAX
  } else {
    2u128.pow(exponent as u32)
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Made `c_int` of `usize` type to prevent overflow if length is large when casting to `nat` and `usize`. Changed `power_of_2_val_concrete` calculation to use the helper function `power_of_2_exec` safely and consistently. Used an appropriate helper to perform checked addition and modulo operations to stay within `u128` limits and for clarity. Changed `val_mod_nat` to `val_mod_exec` since it is used in concrete computation now and ensures that its value is `u128` for concrete operations. Also simplified the handling of `c_int` and `c_int_usize` and how `power_of_2_val_concrete` is computed. */
{
    let a_seq = a@;
    let b_seq = b@;

    let val_a = Str2Int(a_seq);
    let val_b = Str2Int(b_seq);

    let c_int: usize = a_seq.len();
    
    let mut val_mod_exec: u128 = 0;
    let power_of_2_val_concrete: u128 = power_of_2_exec(c_int);
    
    let val_sum_u128: u128 = (val_a as u128).checked_add(val_b as u128).unwrap_or(u128::MAX);

    if c_int > 0 && power_of_2_val_concrete != u128::MAX { // Check for potential overflow of power_of_2_exec
        val_mod_exec = val_sum_u128 % power_of_2_val_concrete;
    } else if c_int == 0 {
        val_mod_exec = val_sum_u128 % power_of_2_exec(1); // 2^0 is 1.
    } else {
        val_mod_exec = val_sum_u128; // If c_int is very large, power_of_2_exec returns u128::MAX, which implies no modulo
    }

    let mut bit_vec = Vec::<char>::new();
    let mut concrete_temp_val: u128 = val_mod_exec;

    let c_int_usize: usize = c_int;

    if concrete_temp_val == 0 && c_int_usize > 0 {
        for _i in 0..c_int_usize
            invariant
                _i <= c_int_usize,
        {
            bit_vec.push('0');
        }
    } else if concrete_temp_val == 0 && c_int_usize == 0 {
        bit_vec.push('0'); // Ensure at least one '0' for c_int = 0, val_mod_exec = 0
    }
    else {
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

    let mut reversed_bit_vec = Vec::<char>::new();
    let mut i: isize = bit_vec.len() as isize - 1;
    while i >= 0
        invariant
            i >= -1,
            reversed_bit_vec.len() as isize + i + 1 == bit_vec.len() as isize,
            reversed_bit_vec.len() as isize <= bit_vec.len() as isize,
        decreases i
    {
        let c = bit_vec.pop().unwrap(); // Use pop for exec code
        reversed_bit_vec.insert(0, c); // Insert at beginning to reverse
        i = i - 1;
    }

    reversed_bit_vec
}
// </vc-code>

fn main() {}
}

