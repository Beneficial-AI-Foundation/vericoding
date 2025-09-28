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

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(ret.0) && valid_bit_string(ret.1),
    str2int(ret.0) == str2int(dividend) / str2int(divisor),
    str2int(ret.1) == str2int(dividend) % str2int(divisor)
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
/* helper modified by LLM (iteration 10): Fixed split_at_exec signature and implementation to compile */
fn split_at_exec(s: Vec<char>, n: usize) -> (Vec<char>, Vec<char>)
    ensures
        let (ref left, ref right) = result;
        left.len() == n && right.len() == s.len() - n
{
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    for i in 0..n {
        left.push(s[i]);
    }
    
    for i in n..s.len() {
        right.push(s[i]);
    }
    
    (left, right)
}

proof fn lemma_split_at_length(s: Seq<char>, n: nat)
    requires 0 <= n <= s.len()
    ensures s.subrange(0, n).len() == n && s.subrange(n, s.len()).len() == s.len() - n
{
}

proof fn lemma_exp_int_add_mul(x: nat, y1: nat, y2: nat)
    ensures exp_int(x, y1 + y2) == exp_int(x, y1) * exp_int(x, y2)
    decreases y1
{
    if y1 > 0 {
        lemma_exp_int_add_mul(x, y1 - 1, y2);
    }
}

proof fn lemma_str2int_zero_length(s: Seq<char>)
    requires valid_bit_string(s), s.len() == 0
    ensures str2int(s) == 0
{
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
/* code modified by LLM (iteration 10): Fixed vector syntax and index access */
{
    if sy.len() == 1 {
        if sy.index(0) == '0' {
            zeros(1)
        } else {
            let (q, r) = div_mod(sx, sz);
            r
        }
    } else {
        let n = sy.len();
        let half_n = n / 2;
        let high = sy.subrange(0, n - half_n);
        let low = sy.subrange(n - half_n, n);
        let base = mod_exp_pow2(sx, high, (n - half_n - 1) as nat, sz.clone());
        let exp_result = mod_exp(sx, low, sz.clone());
        let temp = mul(exp_result, base);
        let (q, r) = div_mod(temp, sz);
        r
    }
}
// </vc-code>


}

fn main() {}