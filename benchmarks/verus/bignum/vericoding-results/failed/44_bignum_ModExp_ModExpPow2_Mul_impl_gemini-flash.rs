// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed this section to adhere to the prompt's requirement for exactly 2 elements, as this helper was not explicitly asked for and could lead to issues. */
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Replaced `nat` and `int` casts with concrete integer literals (0, 1, 2) to resolve compilation errors. */
{
    let sx_seq = sx@;
    let sy_seq = sy@;
    let sz_seq = sz@;

    if sy_seq.len() == 1 && sy_seq.index(0) == '0' as char {
        // x^0 mod m = 1 mod m
        let mut res = Vec::new();
        res.push('1');
        res
    } else if sy_seq.len() == 1 && sy_seq.index(0) == '1' as char {
        // x^1 mod m = x mod m
        let x_int = str2int(sx_seq);
        let m_int = str2int(sz_seq);
        let remainder = (x_int % m_int);

        let mut res_vec = Vec::new();
        if remainder == 0 {
            res_vec.push('0');
        } else {
            let mut temp_rem: nat = remainder;
            while temp_rem > 0
                invariant
                    temp_rem >= 0,
            {
                if temp_rem % 2 == 1 {
                    res_vec.push('1');
                }
                else {
                    res_vec.push('0');
                }
                temp_rem = temp_rem / 2;
            }
            res_vec.reverse();
        }
        res_vec
    } else {
        let sy_int = str2int(sy_seq);
        let sy_div_2_int = sy_int / 2;

        let mut sy_div_2_vec = if sy_div_2_int == 0 {
            vec!['0']
        } else {
            let mut temp: nat = sy_div_2_int;
            let mut vec_chars = Vec::new();
            while temp > 0
                invariant
                    temp >= 0,
            {
                if temp % 2 == 1 {
                    vec_chars.push('1');
                } else {
                    vec_chars.push('0');
                }
                temp = temp / 2;
            }
            vec_chars.reverse();
            vec_chars
        };

        let half_pow_mod_m_vec = mod_exp(sx.clone(), sy_div_2_vec, sz.clone());
        let half_pow_mod_m_seq = half_pow_mod_m_vec@;

        let mut result_vec: Vec<char>;
        if (sy_int % 2) == 0 {
            let product = mul(half_pow_mod_m_seq, half_pow_mod_m_seq);
            let product_int = str2int(product);
            let m_int = str2int(sz_seq);
            let remainder = (product_int % m_int);

            result_vec = Vec::new();
            if remainder == 0 {
                result_vec.push('0');
            } else {
                let mut temp_rem: nat = remainder;
                while temp_rem > 0
                    invariant
                        temp_rem >= 0,
                {
                    if temp_rem % 2 == 1 {
                        result_vec.push('1');
                    } else {
                        result_vec.push('0');
                    }
                    temp_rem = temp_rem / 2;
                }
                result_vec.reverse();
            }
        }
        else {
             let product_half = mul(half_pow_mod_m_seq, half_pow_mod_m_seq);
            let product_half_int = str2int(product_half);
            let sx_int = str2int(sx_seq);
            let m_int = str2int(sz_seq);

            let final_product = ((sx_int * product_half_int) % m_int);

            result_vec = Vec::new();
            if final_product == 0 {
                result_vec.push('0');
            } else {
                let mut temp_rem: nat = final_product;
                while temp_rem > 0
                    invariant
                        temp_rem >= 0,
                {
                    if temp_rem % 2 == 1 {
                        result_vec.push('1');
                    } else {
                        result_vec.push('0');
                    }
                    temp_rem = temp_rem / 2;
                }
                result_vec.reverse();
            }
        }
        result_vec
    }
}
// </vc-code>


}

fn main() {}