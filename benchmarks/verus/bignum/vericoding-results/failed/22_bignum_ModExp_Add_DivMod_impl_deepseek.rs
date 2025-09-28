// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2_int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2_int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) + str2_int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2_int(divisor) > 0,
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2_int(res.0) == str2_int(dividend) / str2_int(divisor) &&
    str2_int(res.1) == str2_int(dividend) % str2_int(divisor),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed signature and implementations */
proof fn lemma_pow_mod_base(x: nat, y: nat, z: nat)
    requires
        z > 1
    ensures
        exp_int(x, y) % z == (if y == 0 { 1nat % z } else { ((x % z) * (exp_int(x, y - 1) % z)) % z })
    decreases y
{
    if y > 0 {
        lemma_pow_mod_base(x, y - 1, z);
    }
}

proof fn lemma_div_mod_identity(dividend: nat, divisor: nat)
    requires
        divisor > 0
    ensures
        dividend == divisor * (dividend / divisor) + dividend % divisor
{
}

proof fn lemma_mod_properties(a: nat, b: nat, c: nat)
    requires
        c > 0
    ensures
        (a * b) % c == ((a % c) * (b % c)) % c
{
}

proof fn lemma_exp_int_properties(x: nat, y: nat)
    decreases y
    ensures
        exp_int(x, y) == (if y == 0 { 1nat } else { x * exp_int(x, y - 1) })
{
    if y > 0 {
        lemma_exp_int_properties(x, y - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2_int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2_int(res@) == exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed compilation error, ensure block formatting */
{
    let mut result: Vec<char> = vec!['1'];
    let mut base = sx;
    let mut exponent = sy;
    let modulus = sz;
    
    while exponent.len() > 0
        invariant
            valid_bit_string(result@),
            valid_bit_string(base@),
            valid_bit_string(exponent@),
            str2_int(result@) == exp_int(str2_int(sx@), str2_int(sy@) - str2_int(exponent@)) % str2_int(modulus@)
    {
        let (div_ex, mod_ex) = div_mod(exponent@, seq!['0', '1']);
        exponent = Vec::from_seq(div_ex);
        
        if mod_ex[0] == '1' {
            let temp_result = add(result@, base@);
            let (div_res, mod_res) = div_mod(temp_result, modulus@);
            result = Vec::from_seq(mod_res);
        }
        
        let temp_base = add(base@, base@);
        let (div_base, mod_base) = div_mod(temp_base, modulus@);
        base = Vec::from_seq(mod_base);
    }
    
    result
}
// </vc-code>


}

fn main() {}