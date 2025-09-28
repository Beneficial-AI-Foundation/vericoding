// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
      0nat 
  } else { 
      2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
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

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
      s.len() == n,
      valid_bit_string(s),
      str2int(s) == 0,
      all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed unused helper functions and related traits. */

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
      valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
      sy.len() > 0 && str2int(sz@) > 1,
  ensures 
      valid_bit_string(res@),
      str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed multiple type mismatch issues by correctly casting between `nat` and `int` where necessary, ensuring all `nat` comparisons and operations are done with naturally-typed values. Also, corrected `into_iter().collect()` errors by converting `Seq<char>` to `Vec<char>` for iteration. */
{
    let one_char_vec: Vec<char> = vec!['1'];
    let zero_char_vec: Vec<char> = vec!['0'];

    let spec_sz_val = str2int(sz.view());
    let spec_sy_val = str2int(sy.view());

    if spec_sy_val == 0 {
        one_char_vec
    } else if (spec_sy_val % 2) == (0 as nat) {
        // y is even, calculate as (x^(y/2))^2 mod z
        let two_char_vec: Vec<char> = vec!['1', '0'];
        let y_div_2_seq = div_mod(sy.view(), two_char_vec.view()).0;
        let y_div_2_vec = y_div_2_seq.to_vec(); // Fixed: Seq<char> does not have into_iter()

        let half_pow_vec = mod_exp(sx.clone(), y_div_2_vec, sz.clone());
        let half_pow_mod_z_seq = div_mod(half_pow_vec.view(), sz.view()).1;
        let final_res_seq = div_mod(half_pow_mod_z_seq, sz.view()).1;
        final_res_seq.to_vec() // Fixed: Seq<char> does not have into_iter()
    } else {
        // y is odd, calculate as x * (x^((y-1)/2))^2 mod z
        let y_minus_1_seq = {
            let sy_val = str2int(sy.view());
            let one_val: nat = 1;
            let y_minus_1_val: nat = (sy_val - one_val);

            proof {
                assert(y_minus_1_val >= 0);
            }
            
            if y_minus_1_val == (0 as nat) {
                seq!['0']
            } else {
                let mut s_vec_local: Vec<char> = Vec::new();
                let mut temp: nat = y_minus_1_val;
                while temp > (0 as nat)
                    invariant
                        temp >= 0
                        ,
                    decreases temp
                {
                    if (temp % 2) == (1 as nat) {
                       s_vec_local.insert(0, '1');
                    } else {
                       s_vec_local.insert(0, '0');
                    }
                    temp = (temp / 2);
                }
                s_vec_local@
            }
        };

        let two_char_vec: Vec<char> = vec!['1', '0'];
        let y_minus_1_div_2_seq = div_mod(y_minus_1_seq, two_char_vec.view()).0;
        let y_minus_1_div_2_vec = y_minus_1_div_2_seq.to_vec(); // Fixed: Seq<char> does not have into_iter()

        let x_mod_z_seq = div_mod(sx.view(), sz.view()).1;
        let x_mod_z_vec = x_mod_z_seq.to_vec(); // Fixed: Seq<char> does not have into_iter()

        let half_pow_vec = mod_exp(sx.clone(), y_minus_1_div_2_vec, sz.clone());
        let half_pow_sq_mod_z_seq = div_mod(half_pow_vec.view(), sz.view()).1;
        let half_pow_sq_mod_z_vec = half_pow_sq_mod_z_seq.to_vec(); // Fixed: Seq<char> does not have into_iter()

        let product_spec_val = str2int(x_mod_z_vec.view()) * str2int(half_pow_sq_mod_z_vec.view());
        let product_string_vec_temp = { 
            let mut product_string_vec_temp_local: Vec<char> = Vec::new();
            let mut temp_product: nat = product_spec_val;
            if temp_product == (0 as nat) {
                product_string_vec_temp_local.push('0');
            } else {
                while temp_product > (0 as nat)
                    invariant
                        temp_product >= 0
                        ,
                    decreases temp_product
                {
                    if (temp_product % 2) == (1 as nat) {
                        product_string_vec_temp_local.insert(0, '1');
                    } else {
                        product_string_vec_temp_local.insert(0, '0');
                    }
                    temp_product = (temp_product / 2);
                }
            }
            product_string_vec_temp_local
        };
        
        div_mod(product_string_vec_temp.view(), sz.view()).1.to_vec() // Fixed: Seq<char> does not have into_iter()
    }
}
// </vc-code>


}

fn main() {}