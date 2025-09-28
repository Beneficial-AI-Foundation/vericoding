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
/* helper modified by LLM (iteration 10): added explicit constructors and fixed type issues */
spec fn bit_string_zero() -> Seq<char> {
    seq!['0']
}

spec fn bit_string_one() -> Seq<char> {
    seq!['1']
}

proof fn lemma_str2int_zero()
    ensures str2int(bit_string_zero()) == 0
{
}

proof fn lemma_str2int_one()
    ensures str2int(bit_string_one()) == 1
{
}

proof fn lemma_exp_int_zero(x: nat)
    ensures exp_int(x, 0) == 1
{
}

proof fn lemma_exp_int_one(x: nat)
    ensures exp_int(x, 1) == x
{
}

proof fn lemma_mod_zero(x: nat, m: nat)
    requires m > 0
    ensures x % m < m
{
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
    /* code modified by LLM (iteration 10): fixed ghost variable syntax error */
    if sy.len() == 0 {
        bit_string_one()
    } else {
        let last_bit = sy@[sy.len() - 1];
        let sy_len_minus_one = (sy.len() - 1) as int;
        let sy_prefix = sy.subrange(0, sy_len_minus_one);
        
        if last_bit == '0' {
            let half_result = mod_exp(sx, sy_prefix, sz);
            let squared = mul(half_result, half_result);
            div_mod(squared, sz).1
        } else {
            let half_result = mod_exp(sx, sy_prefix, sz);
            let squared = mul(half_result, half_result);
            let mod_squared = div_mod(squared, sz).1;
            let multiplied = mul(mod_squared, sx);
            div_mod(multiplied, sz).1
        }
    }
}
// </vc-code>


}

fn main() {}