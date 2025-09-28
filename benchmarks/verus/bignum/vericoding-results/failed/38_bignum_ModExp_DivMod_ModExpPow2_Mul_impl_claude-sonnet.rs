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
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
     (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1),
    str2int(res.0) == str2int(dividend) / str2int(divisor),
    str2int(res.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1,
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases n
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): removed problematic seq_to_vec function and fixed compilation errors */
proof fn lemma_exp_int_properties(x: nat, y: nat)
    ensures
        exp_int(x, 0) == 1,
        y > 0 ==> exp_int(x, y) == x * exp_int(x, (y - 1) as nat),
{
}

proof fn lemma_str2int_empty()
    ensures str2int(seq![]) == 0
{
}

proof fn lemma_mod_exp_base_case(sx: Seq<char>, sz: Seq<char>)
    requires
        valid_bit_string(sx) && valid_bit_string(sz),
        str2int(sz) > 1
    ensures
        exp_int(str2int(sx), 0) % str2int(sz) == 1nat % str2int(sz)
{
    assert(exp_int(str2int(sx), 0) == 1) by {
        lemma_exp_int_properties(str2int(sx), 0);
    }
}

proof fn lemma_mod_exp_recursive(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>)
    requires
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        sy.len() > 0,
        str2int(sz) > 1
    ensures
        sy[sy.len() - 1] == '0' ==> {
            let sy_half = sy.subrange(0, sy.len() - 1);
            exp_int(str2int(sx), str2int(sy)) == exp_int(exp_int(str2int(sx), str2int(sy_half)), 2)
        },
        sy[sy.len() - 1] == '1' ==> {
            let sy_minus_one = sy.subrange(0, sy.len() - 1);
            exp_int(str2int(sx), str2int(sy)) == str2int(sx) * exp_int(str2int(sx), str2int(sy_minus_one))
        }
{
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed Seq indexing and nat casting compilation errors */
    if sy.len() == 1 && sy[0] == '0' {
        proof {
            lemma_mod_exp_base_case(sx@, sz@);
        }
        return vec!['1'];
    }
    
    let last_bit = sy[sy.len() - 1];
    let mut sy_reduced = sy.clone();
    sy_reduced.pop();
    
    if last_bit == '0' {
        let temp_result = mod_exp(sx.clone(), sy_reduced, sz.clone());
        let squared = mul(temp_result@, temp_result@);
        let (_, remainder) = div_mod(squared, sz@);
        proof {
            lemma_mod_exp_recursive(sx@, sy@, sz@);
        }
        let mut result = Vec::new();
        let mut i = 0;
        while i < remainder.len()
            invariant
                0 <= i <= remainder.len(),
                result.len() == i,
                result@ == remainder.subrange(0, i as int),
        {
            result.push(remainder[i as int]);
            i += 1;
        }
        return result;
    } else {
        let temp_result = mod_exp(sx.clone(), sy_reduced, sz.clone());
        let multiplied = mul(sx@, temp_result@);
        let (_, remainder) = div_mod(multiplied, sz@);
        proof {
            lemma_mod_exp_recursive(sx@, sy@, sz@);
        }
        let mut result = Vec::new();
        let mut i = 0;
        while i < remainder.len()
            invariant
                0 <= i <= remainder.len(),
                result.len() == i,
                result@ == remainder.subrange(0, i as int),
        {
            result.push(remainder[i as int]);
            i += 1;
        }
        return result;
    }
}
// </vc-code>


}

fn main() {}