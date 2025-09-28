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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2int(divisor) > 0
  ensures 
    ({
       let (quotient, remainder) = result; 
       valid_bit_string(quotient) && valid_bit_string(remainder) &&
       str2int(quotient) == str2int(dividend) / str2int(divisor) &&
       str2int(remainder) == str2int(dividend) % str2int(divisor)
    })
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
    (str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0) &&
    sy.len() == n + 1 &&
    str2int(sz) > 1
  ensures 
    valid_bit_string(res) &&
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Ensure return type `nat` for `0` and `1`. */
fn get_nth_bit_exec(s: &Vec<char>, n: usize) -> nat {
    if n >= s.len() {
        0nat
    } else {
        if s[s.len() - 1 - n] == '1' {
            1nat
        } else {
            0nat
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type mismatches by ensuring `nat` values are used where expected and replaced `as u128` casts with `as u128;` after ensuring all operands are `u128`.*/
{
    let sy_seq = &sy;
    let sz_seq = sz@;

    if sy_seq.len() == 1 && sy_seq[0] == '0' as char {
        if str2int(sz_seq) <= 1 nat {
            return (vec!['1']);
        }
        return (vec!['1']);
    }

    let b = get_nth_bit_exec(sy_seq, 0);

    if b == 1 nat {
        let mut recurse_sy_vec = Vec::new();
        for i in 0..(sy_seq.len().saturating_sub(1)) {
            recurse_sy_vec.push(sy_seq[i]);
        }
        let recurse_sy = Vec::from(recurse_sy_vec);

        let mut sx_clone = sx.clone();
        let mut sz_clone = sz.clone();
        let temp_res = mod_exp(sx_clone, recurse_sy, sz_clone);
        
        proof {
            let sx_val: nat = str2int(sx@);
            let temp_res_val: nat = str2int(temp_res@);
            let sz_val: nat = str2int(sz_seq);
            let final_val: nat = (sx_val * temp_res_val) % sz_val;
            assert(final_val < sz_val);
        }
        let final_val_exec: u128;
        {
            let sx_val_exec: u128 = str2int(sx@) as u128;
            let temp_res_val_exec: u128 = str2int(temp_res@) as u128;
            let sz_val_exec: u128 = str2int(sz_seq) as u128;
            final_val_exec = (sx_val_exec * temp_res_val_exec) % sz_val_exec;
        }

        let mut result_vec = Vec::new();
        if final_val_exec == 0 {
            result_vec.push('0');
        } else {
            let mut temp: u128 = final_val_exec;
            while temp > 0 
                invariant
                    temp >= 0
            {
                if temp % 2 == 1 {
                    result_vec.push('1');
                } else {
                    result_vec.push('0');
                }
                temp = temp / 2;
            }
            result_vec.reverse();
        }
        result_vec
    } else {
        let mut recurse_sy_vec = Vec::new();
        for i in 0..(sy_seq.len().saturating_sub(1)) {
            recurse_sy_vec.push(sy_seq[i]);
        }
        let recurse_sy = Vec::from(recurse_sy_vec);

        let mut sx_clone = sx.clone();
        let mut sz_clone = sz.clone();
        let temp_res = mod_exp(sx_clone, recurse_sy, sz_clone);

        proof {
            let temp_res_val: nat = str2int(temp_res@);
            let sz_val: nat = str2int(sz_seq);
            let final_val: nat = (temp_res_val * temp_res_val) % sz_val;
            assert(final_val < sz_val);
        }
        let final_val_exec: u128;
        {
            let temp_res_val_exec: u128 = str2int(temp_res@) as u128;
            let sz_val_exec: u128 = str2int(sz_seq) as u128;
            final_val_exec = (temp_res_val_exec * temp_res_val_exec) % sz_val_exec;
        }

        let mut result_vec = Vec::new();
        if final_val_exec == 0 {
            result_vec.push('0');
        } else {
            let mut temp: u128 = final_val_exec;
            while temp > 0 
                invariant
                    temp >= 0
            {
                if temp % 2 == 1 {
                    result_vec.push('1');
                } else {
                    result_vec.push('0');
                }
                temp = temp / 2;
            }
            result_vec.reverse();
        }
        result_vec
    }
}
// </vc-code>


}

fn main() {}