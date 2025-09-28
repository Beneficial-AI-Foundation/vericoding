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
  if y == 0nat { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
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
spec fn int2str(n: nat) -> Seq<char>
  decreases n
{
  if n == 0nat {
    seq!['0']
  } else {
    int2str(n / 2).push(if n % 2 == 1nat { '1' } else { '0' })
  }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  let n1 = str2int(s1);
  let n2 = str2int(s2);
  let sum = n1 + n2;
  int2str(sum)
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0nat,
    sy.len() == n + 1,
    str2int(sz) > 1nat
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  let x = str2int(sx);
  let m = str2int(sz);
  let mut result: nat = 1nat % m;
  if str2int(sy) == 0nat {
    // result already set
  } else {
    result = x % m;
    let mut k = n;
    while k > 0nat 
      invariant 
        valid_bit_string(sz),
        str2int(sz) > 1nat
    {
      result = (result * result) % m;
      k = k - 1;
    }
  }
  int2str(result)
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  let n1 = str2int(s1);
  let n2 = str2int(s2);
  let product = n1 * n2;
  int2str(product)
}

fn zeros(n: nat) -> (res: Seq<char>)
  ensures 
    res.len() == n,
    valid_bit_string(res),
    str2int(res) == 0nat,
    all_zero(res)
{
  let mut s = Seq::<char>::new();
  let mut i = 0nat;
  while i < n 
    invariant 
      s.len() == i,
      valid_bit_string(s),
      all_zero(s)
  {
    s = s.push('0');
    i = i + 1;
  }
  s
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
  if all_zero(sy) {
    let result = 1nat % str2int(sz);
    int2str(result)
  } else {
    let half_pow = mod_exp(sx, sy.subrange(0, sy.len() as int - 1), sz);
    let half_pow_n = str2int(half_pow);
    let result_n = (half_pow_n * half_pow_n) % str2int(sz);
    let mut res: Seq<char> = int2str(result_n);
    if sy[(sy.len() as int - 1) as int] == '1' {
      let x_n = str2int(sx);
      let result_n2 = (result_n * x_n) % str2int(sz);
      res = int2str(result_n2);
    }
    res
  }
}
// </vc-code>


}

fn main() {}