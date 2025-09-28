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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed nat literal syntax by removing nat suffix */
spec fn mod_exp_spec(x: nat, y: nat, z: nat) -> nat
{
    exp_int(x, y) % z
}

proof fn mod_exp_correctness(x: nat, y: nat, z: nat)
    requires z > 1
    ensures mod_exp_spec(x, y, z) < z
{
}

fn int_to_string(n: nat, len: usize) -> (s: Vec<char>)
    ensures
        s@.len() == len,
        valid_bit_string(s@),
        str2int(s@) == n % exp_int(2nat, len as nat)
{
    let mut result = Vec::new();
    let mut remaining = n;
    let mut i = 0;
    
    while i < len
        invariant
            result@.len() == i,
            valid_bit_string(result@),
            i <= len
    {
        let bit = if remaining % 2 == 0 { '0' } else { '1' };
        result.push(bit);
        remaining = remaining / 2;
        i = i + 1;
    }
    
    result
}

fn str2int_exec(s: &Vec<char>) -> (result: nat)
    requires valid_bit_string(s@)
    ensures result == str2int(s@)
{
    let mut result: nat = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result == str2int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    result
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
    /* code modified by LLM (iteration 10): Fixed nat literal syntax by removing nat suffix */
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        let x_mod = str2int_exec(&sx) % str2int_exec(&sz);
        return int_to_string(x_mod, sz.len());
    }
    
    let last_bit = sy[sy.len() - 1];
    let mut sy_half = sy.clone();
    sy_half.pop();
    
    let half_result = mod_exp(sx.clone(), sy_half, sz.clone());
    let squared = (str2int_exec(&half_result) * str2int_exec(&half_result)) % str2int_exec(&sz);
    
    let final_result = if last_bit == '1' {
        (squared * str2int_exec(&sx)) % str2int_exec(&sz)
    } else {
        squared
    };
    
    int_to_string(final_result, sz.len())
}
// </vc-code>


}

fn main() {}