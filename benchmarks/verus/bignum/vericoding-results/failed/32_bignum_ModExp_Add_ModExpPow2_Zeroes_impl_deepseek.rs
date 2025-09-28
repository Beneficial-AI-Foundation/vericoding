// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
      0nat 
  } else { 
      2nat * str2int(s.subrange(0, s.len() as int - 1)) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
      valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
      valid_bit_string(res),
      str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
      valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
      str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
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
/* helper modified by LLM (iteration 10): Remove Vec usage and fix ghost type conversions */
fn zeros_exec(n: u64) -> (s: Seq<char>)
    ensures 
        s.len() == n as nat,
        valid_bit_string(s),
        str2int(s) == 0,
        all_zero(s),
{
    if n == 0 {
        Seq::empty()
    } else {
        let mut result = Seq::empty();
        let mut i: u64 = 0;
        while i < n
            invariant
                i <= n,
                result.len() == i as nat,
                forall|j: int| 0 <= j < i ==> result[j] == '0',
        {
            result = result + Seq::new(1, |k: int| '0');
            i = i + 1;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
      valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
      sy.len() > 0 && str2int(sz) > 1,
  ensures 
      valid_bit_string(res),
      str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Use proper type conversions and avoid sub function */
{
    let n_len = sy.len() as int;
    
    if n_len == 0 {
        return Seq::new(1, |k: int| '1');
    }
    
    if all_zero(sy) {
        return zeros_exec(sz.len() as u64);
    }
    
    let mid = n_len / 2;
    let sy_upper = sy.subrange(0, mid);
    let sy_lower = sy.subrange(mid, n_len);
    
    let upper_result = mod_exp(sx, sy_upper, sz);
    let lower_result = mod_exp(sx, sy_lower, sz);
    
    let combined = add(upper_result, lower_result);
    
    if str2int(combined) < str2int(sz) {
        combined
    } else {
        add(combined, zeros_exec(sz.len() as u64))
    }
}
// </vc-code>


}

fn main() {}