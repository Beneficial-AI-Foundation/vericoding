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

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): added nat suffixes to integer literals to fix mismatched types compilation errors */
spec fn int_to_bit_seq(n: nat) -> (result: Seq<char>)
  ensures
    valid_bit_string(result),
    str2int(result) == n,
    n == 0nat ==> result == seq!['0'],
    n > 0nat ==> result.len() > 0 && result[0] != '0'
  decreases n
{
  if n == 0nat {
    seq!['0']
  } else if n == 1nat {
    seq!['1']
  } else {
    int_to_bit_seq(n / 2nat).add(seq![if n % 2nat == 1nat {'1'} else {'0'}])
  }
}

fn int_to_bit_vec(n: nat) -> (result: Vec<char>)
  ensures
    result@ == int_to_bit_seq(n)
{
  if n == 0nat {
    let mut vec = Vec::with_capacity(1);
    vec.push('0');
    vec
  } else {
    let mut vec = Vec::new();
    let mut current: nat = n;
    while current > 0nat
      invariant
        true,
      decreases current
    {
      let bit = if current % 2nat == 1nat { '1' } else { '0' };
      vec.push(bit);
      current = current / 2nat;
    }
    vec.reverse();  // To have MSB first
    vec
  }
}

proof fn int_to_bit_seq_helper(vec: Seq<char>, remaining: nat) -> Seq<char> {
  // Helper proof function if needed for invariants
  vec
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): no changes, as fixed helpers should resolve compilation */
{
    let n1 = str2int(s1@);
    let n2 = str2int(s2@);
    let res_n = n1 * n2;
    let res = int_to_bit_vec(res_n);
    res
}
// </vc-code>


}

fn main() {}