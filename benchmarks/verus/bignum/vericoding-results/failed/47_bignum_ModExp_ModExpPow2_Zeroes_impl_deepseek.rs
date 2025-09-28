// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
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
  if y == 0 {
    1nat
  } else {
    x * exp_int(x, (y - 1) as nat)
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
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
/* helper modified by LLM (iteration 10): Fix ghost code usage by converting to usize for executable code */
fn mod_exp_pow2_exec(sx: Vec<char>, sy: Vec<char>, n: usize, sz: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
    sy.len() == n + 1,
    str2int(sz@) > 1
  ensures
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases n
{
  if n == 0 {
    if str2int(sy@) == 0nat {
      let zero_seq = zeros(1);
      Vec::from_seq(zero_seq)
    } else {
      let mut res_vec = Vec::new();
      res_vec.push('1');
      res_vec
    }
  } else {
    let half_n = n - 1;
    let half_sy_seq = sy@.subrange(0, half_n as usize);
    let half_sy = Vec::from_seq(half_sy_seq);
    let temp = mod_exp_pow2_exec(sx, half_sy, half_n, sz.clone());
    let squared = mod_exp_pow2_exec(temp.clone(), temp, half_n, sz.clone());
    if sy[half_n] == '1' {
      let one_vec = {
        let mut v = Vec::new();
        v.push('1');
        v
      };
      mod_exp_pow2_exec(squared, one_vec, 0, sz)
    } else {
      squared
    }
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fix ghost code usage by converting to usize for executable code */
{
    let n = sy.len() - 1;
    let mut result = Vec::new();
    result.push('1');
    let mut current_x = sx;
    
    let mut i: usize = 0;
    while i < sy.len()
        invariant
            valid_bit_string(current_x@),
            valid_bit_string(result@),
            str2int(result@) == exp_int(str2int(sx@), str2int(sy@.subrange(0, i as usize))) % str2int(sz@),
            i <= sy.len()
        decreases sy.len() - i
    {
        if sy[i] == '1' {
            let temp = mod_exp_pow2_exec(current_x.clone(), result.clone(), n, sz.clone());
            result = temp;
        }
        
        if i < sy.len() - 1 {
            let squared = mod_exp_pow2_exec(current_x.clone(), current_x.clone(), n, sz.clone());
            current_x = squared;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}