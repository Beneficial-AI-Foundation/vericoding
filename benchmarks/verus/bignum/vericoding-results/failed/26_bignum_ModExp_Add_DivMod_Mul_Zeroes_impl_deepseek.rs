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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1),
    str2int(res.0) == str2int(dividend) / str2int(divisor),
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Remove ghost type usage in executable code and fix type conversions */
fn str_to_int_exec(s: Seq<char>) -> (r: int)
  requires valid_bit_string(s)
  ensures r >= 0, r as nat == str2int(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    let s_len = s.len();
    let prefix = s.subrange(0, s_len - 1);
    let prefix_val = str_to_int_exec(prefix);
    let last_char = s[s_len - 1];
    let last_digit = if last_char == '1' { 1 } else { 0 };
    prefix_val * 2 + last_digit
  }
}

/* helper modified by LLM (iteration 10): Remove ghost type usage and fix parameter types */
proof fn mod_exp_helper(x: nat, y: Seq<char>, z: nat) -> (r: nat)
  requires 
    valid_bit_string(y) && y.len() > 0,
    z > 1
  ensures 
    r == exp_int(x, str2int(y)) % z,
    r < z
  decreases y.len()
{
  if y.len() == 1 {
    let y0 = y[0];
    if y0 == '1' {
      assert(exp_int(x, 1nat) == x);
      x % z
    } else {
      assert(exp_int(x, 0nat) == 1nat);
      1nat % z
    }
  } else {
    let y_len = y.len();
    let half = y.subrange(0, y_len - 1);
    let half_result = mod_exp_helper(x, half, z);
    let last_char = y[y_len - 1];
    if last_char == '1' {
      let squared = (half_result * half_result) % z;
      (squared * x) % z
    } else {
      (half_result * half_result) % z
    }
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fix ghost type usage and implement conversion */
    let x_val = str_to_int_exec(sx);
    let z_val = str_to_int_exec(sz);
    proof {
        assert(z_val > 1) by {
            assert(str2int(sz) > 1);
            assert(z_val as nat == str2int(sz));
        }
    }
    let result_val: nat;
    proof {
        result_val = mod_exp_helper(x_val as nat, sy, z_val as nat);
    }
    if result_val == 0 {
        let n = sz.len();
        zeros(n)
    } else {
        let mut temp = result_val;
        let mut result_vec: Vec<char> = Vec::new();
        while temp > 0 {
            let digit = temp % 2;
            result_vec.push(if digit == 1 { '1' } else { '0' });
            temp = temp / 2;
        }
        result_vec.reverse();
        result_vec.into_iter().collect()
    }
}
// </vc-code>


}

fn main() {}