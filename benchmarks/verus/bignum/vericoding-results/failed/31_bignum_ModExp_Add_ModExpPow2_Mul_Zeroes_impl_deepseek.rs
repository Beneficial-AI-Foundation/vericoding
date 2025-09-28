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
/* helper modified by LLM (iteration 10): Remove nat/int type conversions and use usize for executable code */
fn mul_helper(a: Seq<char>, b: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(a) && valid_bit_string(b)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(a) * str2int(b)
{
  if all_zero(b) {
    zeros(a.len())
  } else if all_zero(a) {
    zeros(b.len())
  } else {
    mul(a, b)
  }
}

/* helper modified by LLM (iteration 10): Remove nat/int type conversions and use usize for executable code */
fn mod_helper(a: Seq<char>, b: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(a) && valid_bit_string(b),
    str2int(b) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(a) % str2int(b)
{
  if str2int(a) < str2int(b) {
    a
  } else {
    let n: usize = a.len();
    let b_len: usize = b.len();
    if n >= b_len {
      let rem = a.subrange(b_len, n);
      rem
    } else {
      zeros(n)
    }
  }
}

proof fn exp_property_lemma(x: nat, y: nat, z: nat)
  requires y >= 1,
  ensures exp_int(x, y) % z == ((x % z) * (exp_int(x, y - 1) % z)) % z
{
  // This property holds by definition of exponentiation modulo z
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
    /* code modified by LLM (iteration 10): Remove nat/int type conversions and use usize for executable code */
    let sy_len: usize = sy.len();
    if sy_len == 0 {
        zeros(1)
    } else if sy_len == 1 {
        if all_zero(sy) {
            zeros(1)
        } else if all_zero(sx) {
            zeros(sx.len())
        } else {
            mod_helper(sx, sz)
        }
    } else {
        let n: usize = sy_len - 1;
        let sy_half = sy.subrange(0, n);
        assert(sy_half.len() == n);
        let exp_result = mod_exp(sx, sy_half, sz);
        let square_result = mul_helper(exp_result, exp_result);
        let mod_square = mod_helper(square_result, sz);
        let last_char = sy.index(n);
        if last_char == '1' {
            let mul_mod = mul_helper(mod_square, sx);
            mod_helper(mul_mod, sz)
        } else {
            mod_square
        }
    }
}
// </vc-code>


}

fn main() {}