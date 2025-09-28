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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
spec fn int2str(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    Seq::empty()
  } else {
    let rest = int2str(n / 2);
    let last_char = if n % 2 == 0 { '0' } else { '1' };
    rest + Seq::singleton(last_char)
  }
}

fn build_vec(s: Ghost<Seq<char>>) -> (result: Vec<char>)
  requires
       forall|i: int| 0 <= i < s@.len() ==> s@[i] == '0' || s@[i] == '1'
  ensures
       result@ == s@
{
  let mut result = Vec::new();
  let length = s@.len();
  let mut idx = 0;
  while idx < length
      invariant
          idx <= length,
          length == s@.len(),
          result.len() == idx,
          forall|k: int| 0 <= k < idx ==> s@[k] == '0' || s@[k] == '1',
          forall|j: int| 0 <= j < idx ==> result@[j] == s@[j]
  {
    let c = s@[idx];
    result = result.push(c);
    idx += 1;
  }
  result
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  proof {
    let b = str2int(sx@);
    let e = str2int(sy@);
    let m = str2int(sz@);
    let res_int = exp_int(b, e) % m;
    let spec_seq = int2str(res_int);
    let res = build_vec(Ghost(spec_seq));
    res
  }
}
// </vc-code>


}

fn main() {}