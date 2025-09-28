// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
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

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
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

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n &&
    valid_bit_string(s) &&
    str2int(s) == 0 &&
    all_zero(s)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): No new helpers are needed here. */

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
/* code modified by LLM (iteration 10): Use `to_vec()` instead of `from_slice` and cast to `int` for `subrange` */
{
    let len_sy = sy.len();
    if len_sy == 1 {
        let y_char = sy[0];
        if y_char == '0' {
            return vec!['1'];
        } else if y_char == '1' {
            let mut res_vec = Vec::new();
            res_vec.extend_from_slice(&sx);
            return res_vec;
        }
    }

    let half_sy_len: usize;
    let mut sy_half: Vec<char>;

    if len_sy % 2 == 0 {
        half_sy_len = len_sy / 2;
        sy_half = sy.subslice(0, half_sy_len).to_vec();
    } else {
        half_sy_len = (len_sy - 1) / 2;
        sy_half = sy.subslice(0, half_sy_len).to_vec();
    }

    let mut temp = mod_exp(sx, sy_half, sz);
    let mul_res = mul(temp@, temp@);
    let mod_res =  mul_res.subrange(0, mul_res.len() as int).to_vec();

    if len_sy % 2 == 1 {
        let mul_x_res = mul(sx@, mod_res@);
        mul_x_res.subrange(0, mul_x_res.len() as int).to_vec()
    } else {
        mod_res
    }
}
// </vc-code>


}

fn main() {}