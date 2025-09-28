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
/* helper modified by LLM (iteration 10): Fixed seq_to_vec to use proper usize indexing and access sequences by index */
proof fn lemma_exp_decomposition(x: nat, y: nat)
  requires y > 0
  ensures exp_int(x, y) == x * exp_int(x, (y - 1) as nat)
{
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn lemma_str2int_single_bit(bit: char)
  requires bit == '0' || bit == '1'
  ensures str2int(seq![bit]) == if bit == '1' { 1nat } else { 0nat }
{
}

proof fn lemma_exp_power_of_2(n: nat)
  ensures exp_int(2nat, n) == if n == 0 { 1nat } else { 2nat * exp_int(2nat, (n - 1) as nat) }
{
}

proof fn lemma_valid_bit_string_last_bit(s: Seq<char>)
  requires valid_bit_string(s), s.len() > 0
  ensures s[s.len() - 1] == '0' || s[s.len() - 1] == '1'
{
}

proof fn lemma_bit_value_zero_or_one(bit: char)
  requires bit == '0' || bit == '1'
  ensures (if bit == '1' { 1nat } else { 0nat }) <= 1
{
}

fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
  requires valid_bit_string(s)
  ensures v@ == s && valid_bit_string(v@)
{
  let mut v = Vec::new();
  let mut i: usize = 0;
  while i < s.len()
    invariant
      0 <= i <= s.len(),
      v.len() == i,
      v@ == s.subrange(0, i as int),
      valid_bit_string(v@)
    decreases s.len() - i
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
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): Fixed 1nat to 1 and seq indexing */
  if sy.len() == 1 {
    if sy[0] == '0' {
      proof {
        lemma_str2int_single_bit(sy[0]);
      }
      let one_bit = vec!['1'];
      one_bit
    } else {
      proof {
        lemma_str2int_single_bit(sy[0]);
      }
      let sx_seq = sx@;
      let sz_seq = sz@;
      let temp_res = mod_exp_pow2(sx_seq, seq!['0', '1'], 1, sz_seq);
      seq_to_vec(temp_res)
    }
  } else {
    let mut sy_half = Vec::new();
    let mut i: usize = 0;
    while i < sy.len() - 1
      invariant
        0 <= i <= sy.len() - 1,
        sy_half.len() == i,
        valid_bit_string(sy_half@),
        forall|j: int| 0 <= j < i ==> sy_half[j] == sy[j]
      decreases sy.len() - 1 - i
    {
      sy_half.push(sy[i]);
      i += 1;
    }
    
    let rec_res = mod_exp(sx.clone(), sy_half, sz.clone());
    let squared = mul(rec_res@, rec_res@);
    
    if sy[sy.len() - 1] == '0' {
      seq_to_vec(squared)
    } else {
      let temp_mul = mul(squared, sx@);
      seq_to_vec(temp_mul)
    }
  }
}
// </vc-code>


}

fn main() {}