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
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(ret.0) && valid_bit_string(ret.1) &&
    str2int(ret.0) == str2int(dividend) / str2int(divisor) &&
    str2int(ret.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed ghost type usage in vec_from_seq */
spec fn seq_from_vec(v: Vec<char>) -> Seq<char> {
    v@
}

proof fn lemma_exp_div_2(x: nat, y: nat)
    requires y > 0
    ensures exp_int(x, y / 2) * exp_int(x, y / 2) == exp_int(x, y / 2 * 2)
{
    reveal(exp_int);
}

proof fn lemma_exp_mod_2(x: nat, y: nat)
    requires y > 0, y >= 1
    ensures y % 2 == 1 ==> exp_int(x, y) == x * exp_int(x, (y - 1) as nat)
{
    reveal(exp_int);
}

fn bit_string_zero() -> (res: Vec<char>)
    ensures valid_bit_string(res@) && str2int(res@) == 0
{
    vec!['0']
}

fn bit_string_one() -> (res: Vec<char>)
    ensures valid_bit_string(res@) && str2int(res@) == 1
{
    vec!['1']
}

fn vec_from_seq(s: Seq<char>) -> (res: Vec<char>)
    ensures res@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == s[j]
    {
        v.push(s[i as int]);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed ghost type comparison */
    if sy.len() == 0 {
        return bit_string_one();
    }
    
    let binary_two = vec!['1', '0'];
    let (y_div_2, y_mod_2) = div_mod(sy@, binary_two@);
    
    let temp_result = mod_exp(sx.clone(), vec_from_seq(y_div_2), sz.clone());
    let squared = mul(temp_result@, temp_result@);
    let (_, base_result) = div_mod(squared, sz@);
    
    proof {
        let y_mod_val = str2int(y_mod_2);
        let is_odd = y_mod_val == 1nat;
    }
    
    if str2int(y_mod_2) == 1 {
        let temp_mul = mul(sx@, base_result);
        let (_, final_result) = div_mod(temp_mul, sz@);
        vec_from_seq(final_result)
    } else {
        vec_from_seq(base_result)
    }
}
// </vc-code>


}

fn main() {}