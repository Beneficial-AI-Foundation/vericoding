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
/* helper modified by LLM (iteration 10): Corrected type casting for subrange arguments. */
fn mod_exp_helper(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1
  ensures
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
{
    // Base case: y is '0'
    if sy.len() == 1 && sy.index(0) == '0' {
        // x^0 mod z = 1 mod z
        let one_seq = Seq::new(1, |i: int| '1');
        let (q, r) = div_mod(one_seq, sz);
        r
    } else {
        // If y is even (last digit is '0')
        if sy.index((sy.len() - 1) as int) == '0' {
            let sy_half = sy.subrange(0, (sy.len() - 1) as int);
            let inner_res_pow = mod_exp_helper(sx, sy_half, sz);
            // (x^(y/2))^2 mod z
            let res_mult = mul(inner_res_pow, inner_res_pow);
            let (q, r) = div_mod(res_mult, sz);
            r
        } else {
            // If y is odd (last digit is '1')
            let sy_minus_1 = sy.subrange(0, (sy.len() - 1) as int);
            let inner_res_pow = mod_exp_helper(sx, sy_minus_1, sz);
            // (x^(y-1) * x) mod z = ((x^(y-1) mod z) * (x mod z)) mod z
            let (sx_mod_z_q, sx_mod_z_r) = div_mod(sx, sz);
            let res_mult = mul(inner_res_pow, sx_mod_z_r);
            let (q, r) = div_mod(res_mult, sz);
            r
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
/* code modified by LLM (iteration 10): Calls the helper function for modular exponentiation. */
{
  // Call the recursive helper function
  mod_exp_helper(sx, sy, sz)
}
// </vc-code>


}

fn main() {}