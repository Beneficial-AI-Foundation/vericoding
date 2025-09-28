// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
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
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed nat/int type errors by using ghost variables */

spec fn is_power_of_two(n: nat) -> bool {
    n > 0 && exists|k: nat| n == exp_int(2nat, k)
}

spec fn log2_floor(n: nat) -> nat
    requires n > 0
    decreases n
{
    if n == 1 { 0 } else { 1 + log2_floor(n / 2) }
}

fn is_zero(s: Seq<char>) -> (res: bool)
    requires valid_bit_string(s)
    ensures res <==> str2int(s) == 0
{
    s.len() == 0nat || forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn is_one(s: Seq<char>) -> (res: bool)
    requires valid_bit_string(s)
    ensures res <==> str2int(s) == 1
{
    s.len() == 1nat && s[0] == '1'
}

fn mod_op(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
        str2int(s2) > 0
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) % str2int(s2)
{
    let (_, remainder) = div_mod(s1, s2);
    remainder
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
    /* code modified by LLM (iteration 10): Fixed compilation error by removing ghost variable and using direct length calculation */
    if is_zero(sy) {
        seq!['1']
    } else if is_one(sy) {
        mod_op(sx, sz)
    } else {
        let last_bit = sy[sy.len() - 1];
        let sy_half = sy.subrange(0, sy.len() - 1);
        let half_result = mod_exp(sx, sy_half, sz);
        let squared = mul(half_result, half_result);
        let squared_mod = mod_op(squared, sz);
        
        if last_bit == '0' {
            squared_mod
        } else {
            let temp = mul(squared_mod, sx);
            mod_op(temp, sz)
        }
    }
}
// </vc-code>


}

fn main() {}