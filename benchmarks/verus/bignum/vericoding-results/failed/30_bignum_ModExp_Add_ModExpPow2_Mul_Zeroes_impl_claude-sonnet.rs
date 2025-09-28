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
/* helper modified by LLM (iteration 10): fixed type annotations for nat literals and added proper type casting */
proof fn lemma_exp_int_zero(x: nat)
    ensures exp_int(x, 0) == 1
{
}

proof fn lemma_exp_int_one(x: nat)
    ensures exp_int(x, 1) == x
{
}

proof fn lemma_exp_int_sum(x: nat, a: nat, b: nat)
    ensures exp_int(x, a + b) == exp_int(x, a) * exp_int(x, b)
    decreases a + b
{
    if a == 0 {
        lemma_exp_int_zero(x);
    } else if b == 0 {
        lemma_exp_int_zero(x);
    } else {
        lemma_exp_int_sum(x, (a - 1) as nat, b);
    }
}

proof fn lemma_mod_exp_zero(x: nat, m: nat)
    requires m > 1
    ensures exp_int(x, 0) % m == 1nat % m
{
    lemma_exp_int_zero(x);
}

proof fn lemma_str2int_subrange(s: Seq<char>)
    requires valid_bit_string(s), s.len() > 0
    ensures str2int(s) == 2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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
{
    /* code modified by LLM (iteration 10): fixed nat type usage by using ghost variables and proper executable variables */
    if sy.len() == 1 {
        if sy[0] == '0' {
            seq!['1']
        } else {
            mod_exp_pow2(sx, sy, 0, sz)
        }
    } else {
        let sy_len_minus_1 = sy.len() - 1;
        let sy_prefix = sy.subrange(0, sy_len_minus_1 as int);
        let last_bit = sy[sy_len_minus_1 as int];
        
        let partial_result = mod_exp(sx, sy_prefix, sz);
        let squared = mul(partial_result, partial_result);
        
        if last_bit == '0' {
            squared
        } else {
            let sx_mod = mod_exp_pow2(sx, seq!['1'], 0, sz);
            mul(squared, sx_mod)
        }
    }
}
// </vc-code>


}

fn main() {}