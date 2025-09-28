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
/* helper modified by LLM (iteration 10): Fixed compilation error by adding missing comma in seq_len_to_usize function signature */
proof fn lemma_exp_int_zero(x: nat)
    ensures exp_int(x, 0nat) == 1nat
{
}

proof fn lemma_exp_int_one(x: nat)
    ensures exp_int(x, 1nat) == x
{
}

proof fn lemma_str2int_zeros(n: nat)
    ensures str2int(zeros(n)) == 0nat
{
}

proof fn lemma_mod_exp_pow2_correct(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
        sy.len() == n + 1,
        str2int(sz) > 1
    ensures
        str2int(mod_exp_pow2(sx, sy, n, sz)) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
{
}

fn seq_len_to_usize(s: Seq<char>) -> (result: usize)
    requires s.len() < 0x10000000000000000
    ensures result as nat == s.len()
{
    s.len() as usize
}

fn seq_index(s: Seq<char>, i: usize) -> (result: char)
    requires 
        i as nat < s.len()
    ensures result == s[i as int]
{
    s[i as int]
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
    /* code modified by LLM (iteration 10): Fixed compilation error by adding missing comma in function call */
    let sy_len = seq_len_to_usize(sy);
    if sy_len == 1 {
        let first_char = seq_index(sy, 0);
        if first_char == '0' {
            let one = seq!['1'];
            one
        } else {
            let base_mod = sx;
            base_mod
        }
    } else {
        let mid = sy_len / 2;
        let sy_low = sy.subrange(0, mid as int);
        let sy_high = sy.subrange(mid as int, sy_len as int);
        
        let temp1 = mod_exp(sx, sy_low, sz);
        let temp2 = mod_exp(sx, sy_high, sz);
        let result = mul(temp1, temp2);
        result
    }
}
// </vc-code>


}

fn main() {}