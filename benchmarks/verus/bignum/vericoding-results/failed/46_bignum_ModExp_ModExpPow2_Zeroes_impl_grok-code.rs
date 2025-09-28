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
/* helper modified by LLM (iteration 8): no changes, helpers are correct */
fn int2str(n: nat) -> (s: Seq<char>)
  ensures 
    valid_bit_string(s),
    str2int(s) == n
  decreases n
{
  if n == 0nat {
    Seq::empty()
  } else {
    let rem = n / 2nat;
    let rest = int2str(rem);
    let msb = if n % 2nat == 0nat { '0' } else { '1' };
    Seq::concat(rest, seq![msb])
  }
}

fn mod_pow_impl(x: nat, e: nat, m: nat) -> (r: nat)
  requires m > 1nat
  ensures r == exp_int(x, e) % m
  decreases e
{
  if e == 0nat {
    1nat
  } else if e % 2nat == 0nat {
    let xx = ((x % m) * (x % m)) % m;
    let half = mod_pow_impl(xx, e / 2nat, m);
    (half * half) % m
  } else {
    let rest = mod_pow_impl(x, e - 1nat, m);
    ((x % m) * rest) % m
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
/* code modified by LLM (iteration 8): made len and i ghost to fix 'int' usage in exec code */
{
  let a = str2int(sx@);
  let exp_ = str2int(sy@);
  let mod_ = str2int(sz@);
  let res_int = mod_pow_impl(a, exp_, mod_);
  let res_seq = int2str(res_int);
  let mut res_vec = Vec::new();
  ghost let len = res_seq.len();
  ghost let mut i = 0;
  while i < len
    invariant
      res_vec@ == res_seq.subrange(0, i),
      0 <= i <= len
    decreases len - i
  {
    res_vec.push(res_seq[i]);
    i = i + 1;
  }
  res_vec
}
// </vc-code>


}

fn main() {}