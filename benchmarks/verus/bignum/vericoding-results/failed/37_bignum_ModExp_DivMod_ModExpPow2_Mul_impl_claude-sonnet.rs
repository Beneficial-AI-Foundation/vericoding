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
/* helper modified by LLM (iteration 10): fixed index access to use usize for execution */
fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
  requires valid_bit_string(s)
  ensures 
    valid_bit_string(res@),
    res@ == s
{
  let mut result = Vec::new();
  let mut i: usize = 0;
  while i < s.len() as usize
    invariant 
      0 <= i <= s.len(),
      result.len() == i,
      valid_bit_string(result@),
      result@ == s.subrange(0, i as int)
  {
    result.push(s[i]);
    i = i + 1;
  }
  result
}

fn create_power_of_2(n: usize) -> (res: Vec<char>)
  requires n < usize::MAX
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(2, n as nat),
    res@.len() == n + 1
{
  let mut result = Vec::new();
  let mut i = 0;
  while i <= n
    invariant 
      0 <= i <= n + 1,
      result.len() == i,
      valid_bit_string(result@)
  {
    if i == n {
      result.push('1');
    } else {
      result.push('0');
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
  /* code modified by LLM (iteration 10): fixed sequence indexing to use usize for execution */
  if str2int(sy@) == 0nat {
    let mut result = Vec::new();
    result.push('1');
    return result;
  }
  
  if str2int(sy@) == 1nat {
    let (_, remainder) = div_mod(sx@, sz@);
    return seq_to_vec(remainder);
  }
  
  let bit_len = sy.len();
  let power_of_2 = create_power_of_2(bit_len - 1);
  
  if str2int(sy@) >= str2int(power_of_2@) {
    let remaining_exp = {
      let mut result = Vec::new();
      let mut i: usize = 0;
      while i < sy.len() as usize
        invariant 0 <= i <= sy.len()
      {
        let sy_bit = sy[i];
        let pow2_bit = power_of_2[i];
        result.push(if sy_bit == '1' && sy_bit != pow2_bit { '1' } else { '0' });
        i = i + 1;
      }
      result
    };
    
    let base_power = {
      proof {
        let n_ghost: nat = (bit_len - 1) as nat;
        assert(str2int(power_of_2@) == exp_int(2, n_ghost));
      }
      mod_exp_pow2(sx@, power_of_2@, {
        proof {
          (bit_len - 1) as nat
        }
      }, sz@)
    };
    let remaining_power = mod_exp(sx, remaining_exp, sz.clone());
    let product = mul(base_power, remaining_power@);
    let (_, final_remainder) = div_mod(product, sz@);
    seq_to_vec(final_remainder)
  } else {
    let smaller_power = create_power_of_2(bit_len - 2);
    proof {
      let n_ghost: nat = (bit_len - 2) as nat;
      assert(str2int(smaller_power@) == exp_int(2, n_ghost));
    }
    seq_to_vec(mod_exp_pow2(sx@, smaller_power@, {
      proof {
        (bit_len - 2) as nat
      }
    }, sz@))
  }
}
// </vc-code>


}

fn main() {}