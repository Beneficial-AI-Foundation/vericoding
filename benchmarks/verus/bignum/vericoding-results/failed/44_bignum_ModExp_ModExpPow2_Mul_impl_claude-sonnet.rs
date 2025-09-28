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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
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
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): wrapped all nat/int casts in proof blocks to fix compilation errors */
fn mod_exp_bit(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>, bit_pos: usize) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    bit_pos < sy.len(),
    str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy.subrange(bit_pos as int, sy.len() as int))) % str2int(sz)
  decreases sy.len() - bit_pos
{
  if bit_pos == sy.len() - 1 {
    let bit_char = sy[bit_pos as usize];
    if bit_char == '1' {
      sx
    } else {
      seq!['1']
    }
  } else {
    let power_of_2 = sy.len() - bit_pos - 1;
    let bit_char = sy[bit_pos as usize];
    if bit_char == '1' {
      let base_result = mod_exp_bit(sx, sy, sz, bit_pos + 1);
      let power_vec = seq!['1'].add(seq!['0'; power_of_2]);
      proof {
        let power_nat: nat = power_of_2 as nat;
      }
      let sx_power = proof {
        mod_exp_pow2(sx, power_vec, power_of_2 as nat, sz)
      };
      mul(sx_power, base_result)
    } else {
      mod_exp_bit(sx, sy, sz, bit_pos + 1)
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
/* code modified by LLM (iteration 10): wrapped all nat/int casts in proof blocks to fix compilation errors */
{
  if sy.len() == 0 {
    vec!['1']
  } else {
    let sx_seq = sx@;
    let sy_seq = sy@;
    let sz_seq = sz@;
    let result_seq = mod_exp_bit(sx_seq, sy_seq, sz_seq, 0);
    let mut result_vec = vec![];
    let mut i: usize = 0;
    while i < result_seq.len()
      invariant
        i <= result_seq.len(),
        result_vec.len() == i,
        forall|j: int| 0 <= j < i ==> result_vec@[j] == result_seq[j]
    {
      result_vec.push(result_seq[i as usize]);
      i = i + 1;
    }
    result_vec
  }
}
// </vc-code>


}

fn main() {}