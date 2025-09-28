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
/* helper modified by LLM (iteration 10): fixed type compatibility issues */
spec fn bit_is_one(s: Seq<char>, i: int) -> bool
  requires 0 <= i < s.len(), valid_bit_string(s)
{
  s[i] == '1'
}

proof fn lemma_str2int_decomposition(s: Seq<char>)
  requires valid_bit_string(s), s.len() > 0
  ensures str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
{
}

proof fn lemma_exp_int_base_cases(x: nat, y: nat)
  ensures y == 0 ==> exp_int(x, y) == 1nat,
          y == 1 ==> exp_int(x, y) == x
{
}

proof fn lemma_exp_int_split(x: nat, y1: nat, y2: nat)
  requires y2 > 0
  ensures exp_int(x, y1 + y2) == exp_int(x, y1) * exp_int(x, y2)
  decreases y2
{
  if y2 > 1 {
    lemma_exp_int_split(x, y1, (y2 - 1) as nat);
  }
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
  /* code modified by LLM (iteration 10): fixed nat/int usage by using usize for indices */
  if sy.len() == 1 {
    if sy.index(0) == '0' {
      seq!['1']
    } else {
      let (_, remainder) = div_mod(sx, sz);
      remainder
    }
  } else {
    let half_len = sy.len() / 2;
    let sy_low = sy.subrange(0, half_len);
    let sy_high = sy.subrange(half_len, sy.len());
    
    let res_low = mod_exp(sx, sy_low, sz);
    let res_high = mod_exp(sx, sy_high, sz);
    
    let temp = mul(res_low, res_high);
    let (_, final_res) = div_mod(temp, sz);
    final_res
  }
}
// </vc-code>


}

fn main() {}