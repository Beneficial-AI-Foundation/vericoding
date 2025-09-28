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
    /* code modified by LLM (iteration 10): Fixed syntax error - removed parentheses from assert statements */
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    let mut result = vec!['1'];
    let mut base = sx.clone();
    let mut exp = sy.clone();
    
    while exp.len() > 0 && !(exp.len() == 1 && exp[0] == '0')
        invariant
            valid_bit_string(result@),
            valid_bit_string(base@),
            valid_bit_string(exp@),
            str2int(sz@) > 1,
            str2int(result@) * exp_int(str2int(base@), str2int(exp@)) % str2int(sz@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
        decreases exp@.len()
    {
        if exp[exp.len() - 1] == '1' {
            let temp = mul(result@, base@);
            let (_, rem) = div_mod(temp, sz@);
            let mut rem_vec = Vec::new();
            let rem_len = rem.len() as usize;
            let mut j: usize = 0;
            while j < rem_len
                invariant
                    0 <= j <= rem_len,
                    rem_vec@.len() == j as nat,
                    forall|k: int| 0 <= k < j as int ==> rem_vec@[k] == rem[k as int],
            {
                proof {
                    assert(j as int < rem.len());
                }
                let ch = if rem[j as int] == '1' { '1' } else { '0' };
                rem_vec.push(ch);
                j = j + 1;
            }
            result = rem_vec;
        }
        
        let base_squared = mul(base@, base@);
        let (_, base_mod) = div_mod(base_squared, sz@);
        let mut base_vec = Vec::new();
        let base_mod_len = base_mod.len() as usize;
        let mut j: usize = 0;
        while j < base_mod_len
            invariant
                0 <= j <= base_mod_len,
                base_vec@.len() == j as nat,
                forall|k: int| 0 <= k < j as int ==> base_vec@[k] == base_mod[k as int],
        {
            proof {
                assert(j as int < base_mod.len());
            }
            let ch = if base_mod[j as int] == '1' { '1' } else { '0' };
            base_vec.push(ch);
            j = j + 1;
        }
        base = base_vec;
        
        let exp_seq = exp@;
        let mut new_exp = Vec::new();
        let mut i: usize = 0;
        while i < exp.len() - 1
            invariant
                0 <= i <= exp.len() - 1,
                new_exp@.len() == i as nat,
                forall|j: int| 0 <= j < i as int ==> new_exp@[j] == exp_seq[j],
                valid_bit_string(new_exp@),
        {
            new_exp.push(exp[i]);
            i = i + 1;
        }
        exp = new_exp;
    }
    
    result
}
// </vc-code>


}

fn main() {}