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
/* helper modified by LLM (iteration 10): Ensure that `int_to_str` produces at least '0' for input '0'. */
fn mod_fn(s: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires
    valid_bit_string(s) && valid_bit_string(sz),
    str2int(sz) > 1
  ensures
    valid_bit_string(res),
    str2int(res) == str2int(s) % str2int(sz)
{
  let s_int = str2int(s);
  let sz_int = str2int(sz);
  let mut current_s = s.clone();

  while str2int(current_s) >= sz_int
    invariant
      valid_bit_string(current_s),
      str2int(current_s) <= s_int,
      str2int(current_s) % sz_int == s_int % sz_int,
      str2int(current_s) >= 0
    decreases str2int(current_s)
  {
    let val_after_sub: nat = (str2int(current_s) - sz_int);
    current_s = int_to_str(val_after_sub);
  }
  current_s
}

fn int_to_str(x_nat: nat) -> (s_res: Seq<char>)
  ensures
    str2int(s_res) == x_nat,
    valid_bit_string(s_res)
{
  if x_nat == 0 {
    return seq!['0'];
  }

  let mut x: nat = x_nat;
  let mut s: Seq<char> = Seq::empty();
  while x > 0
    invariant
      x >= 0
    decreases x
  {
    if x % 2 == 1 { // Use nat for modulo operation if x is nat
      s = s.push('1');
    } else {
      s = s.push('0');
    }
    x = x / 2;
  }
  let mut reversed_s: Seq<char> = Seq::empty();
  let mut i = s.len();
  while i > 0
    invariant
      s.len() == (i + reversed_s.len()),
      0 <= i,
      i <= s.len()
    decreases i
  {
    i = i - 1;
    reversed_s = reversed_s.push(s[i]);
  }
  reversed_s
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
/* code modified by LLM (iteration 10): Removed direct `nat` casting for `sy_len_nat` and the argument to `int_to_str` in `two_str` to fix compilation errors. The `n` parameter for `mod_exp_pow2` remains `nat` and is correctly passed. */
{
  let sy_val = str2int(sy);
  if sy_val == 0 {
    seq!['1']
  } else {
    let sy_len_u64: u64 = sy.len().reveal_value();
    let sy_minus_1_char = 
        if sy_len_u64 == 1 {
            seq!['0']
        } else {
            sy.subrange(0, (sy_len_u64 - 1))
        };
    
    let last_bit = sy[sy_len_u64 - 1];

    let res_recursive = mod_exp(sx /* x */, sy_minus_1_char, sz);
    
    let two_str = int_to_str(2nat);
    let squared_res = mod_exp_pow2(res_recursive, two_str, sy_len_u64 as nat, sz);

    if last_bit == '1' {
      let multiplied_res = mul(squared_res, sx);
      mod_fn(multiplied_res, sz)
    } else {
      mod_fn(squared_res, sz)
    }
  }
}
// </vc-code>


}

fn main() {}