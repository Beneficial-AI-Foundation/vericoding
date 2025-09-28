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
/* helper modified by LLM (iteration 4): updated int_to_seq and mul_mod to use nat literals, changed mod_exp_helper to take len as int and build Vec for subrange manually, implemented zeros as spec fn without assume */
spec fn zeros(n: nat) -> (s: Seq<char>)
  ensures
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s),
  decreases n
{
  if n == 0nat { seq![] } else { zeros(n - 1nat).push('0') }
}

fn int_to_seq(n: nat) -> (result: Vec<char>)
  ensures
    valid_bit_string(result@),
    all_zero(result@) && str2int(result@) == 0 || (!all_zero(result@) && str2int(result@) == n),
    (n == 0nat && result@ == seq!['0']) || n > 0nat,
{
  let mut res: Vec<char> = Vec::new();
  if n == 0nat {
    res.push('0');
  } else {
    let mut m = n;
    while m > 0nat
      invariant
        m >= 0nat,
      decreases m
    {
      res.push(if m % 2nat == 1nat { '1' } else { '0' });
      m = m / 2nat;
    }
    res.reverse();
  }
  res
}

fn mul_mod(a: Seq<char>, b: Seq<char>, modulus: Seq<char>) -> (result: Vec<char>)
  requires
    valid_bit_string(a),
    valid_bit_string(b),
    valid_bit_string(modulus),
    str2int(modulus) > 1,
  ensures
    valid_bit_string(result@),
    str2int(result@) == (str2int(a) * str2int(b)) % str2int(modulus),
{
  int_to_seq(((str2int(a) * str2int(b)) % str2int(modulus)))
}

fn mod_exp_helper(base: Vec<char>, exp: Vec<char>, modulus: Vec<char>, len: int) -> (result: Vec<char>)
  requires
    valid_bit_string(base@),
    valid_bit_string(exp@),
    valid_bit_string(modulus@),
    str2int(modulus@) > 1,
    len >= 0,
    exp@.len() == len,
  ensures
    valid_bit_string(result@),
    str2int(result@) == exp_int(str2int(base@), str2int(exp@)) % str2int(modulus@),
  decreases len
{
  if len == 0 {
    vec!['1']
  } else {
    let bit = exp[len - 1];
    let low = len - 1;
    let mut sy_half = Vec::new();
    let mut i = 0;
    while i < low
      invariant
        0 <= i <= low,
      decreases low - i
    {
      sy_half.push(exp[i]);
      i = i + 1;
    }
    let half_res = mod_exp_helper(base, sy_half, modulus, low);
    let squared = mul_mod(half_res@, half_res@, modulus@);
    if bit == '0' {
      squared
    } else {
      let base_mod = mul_mod(seq!['1'], base@, modulus@);
      mul_mod(base_mod@, squared@, modulus@)
    }
  }
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
/* code modified by LLM (iteration 4): called mod_exp_helper with updated signature */
mod_exp_helper(sx, sy, sz, sy@.len())
}
// </vc-code>


}

fn main() {}