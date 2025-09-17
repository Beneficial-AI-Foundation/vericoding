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
/* helper modified by LLM (iteration 8): Added an exec function to compute powers of 2 for use in concrete code */
fn power_of_2_exec(exponent: usize) -> (result: u128)
  ensures result == (2u128).checked_pow(exponent as u32).unwrap_or(0)
{
  (2u128).checked_pow(exponent as u32).unwrap_or(0)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): Corrected multiple type mismatches by primarily using `u128` for concrete arithmetic and introduced a `power_of_2_exec` helper for `2^c_int`. Adjusted `nat` to `int` and `usize` castings as needed, and resolved `ptracked_remove` to `pop` and `insert`. Also, fixed concrete loop for generating bit strings from `concrete_temp_val`. */
{
    let a_seq = a@;
    let b_seq = b@;

    let val_a = Str2Int(a_seq);
    let val_b = Str2Int(b_seq);

    let c_int: int = a_seq.len() as int;
    
    let mut val_mod_nat: nat = 0;
    let mut power_of_2_val_concrete: u128 = 0;

    proof {
        let val_sum_nat = val_a + val_b;

        if c_int >= 0 {
            let mut power_nat: nat = 1; 
            let mut i_nat: nat = 0;
            while i_nat < c_int as nat
                invariant
                    i_nat <= c_int as nat,
                    power_nat == (2_nat).pow(i_nat as nat),
                decreases (c_int as nat) - i_nat
            {
                power_nat = power_nat * 2;
                i_nat = i_nat + 1;
            }
            val_mod_nat = val_sum_nat % power_nat;
        } else {
            val_mod_nat = val_sum_nat;
        }
    }

    let mut bit_vec = Vec::<char>::new();
    let mut concrete_temp_val: u128 = val_mod_nat as u128;

    let c_int_usize: usize = if c_int < 0 { 0 } else { c_int as usize };

    if concrete_temp_val == 0 && c_int > 0 {
        for _i in 0..c_int_usize
            invariant
                _i <= c_int_usize,
        {
            bit_vec.push('0');
        }
    } else if concrete_temp_val == 0 && c_int == 0 {
        bit_vec.push('0');
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

