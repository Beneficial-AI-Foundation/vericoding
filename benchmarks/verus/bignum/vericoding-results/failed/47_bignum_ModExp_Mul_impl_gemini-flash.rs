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
  if y == 0 {
    1nat
  } else {
    x * exp_int(x, (y - 1) as nat)
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed nat literals, as `nat` is already a numeric type in spec fn */
spec fn mod_rec(x_val: nat, y_val: nat, z_val: nat) -> nat
    decreases y_val
{
    if y_val == 0 {
        1
    } else if y_val == 1 {
        x_val % z_val
    }else {
        let half_y = y_val / 2;
        let half_res = mod_rec(x_val, half_y, z_val);
        if y_val % 2 == 0 {
            (half_res * half_res) % z_val
        } else {
            (x_val * half_res * half_res) % z_val
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Casted integer literals to `nat` where needed */
{
    let x_val = str2int(sx@);
    let y_val = str2int(sy@);
    let z_val = str2int(sz@);

    let result_val = mod_rec(x_val, y_val, z_val);

    // Convert nat to Vec<char> representing the bit string
    let mut result_vec = Vec::new();
    if result_val == (0 as nat) {
        result_vec.push('0');
    } else {
        let mut temp_val = result_val;
        while temp_val > (0 as nat)
            invariant
                temp_val <= result_val
            decreases temp_val
        {
            if temp_val % (2 as nat) == (1 as nat) {
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            temp_val = temp_val / (2 as nat);
        }
        result_vec.reverse();
    }
    
    result_vec
}
// </vc-code>


}

fn main() {}