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

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires valid_bit_string(s1) && valid_bit_string(s2)
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
/* helper modified by LLM (iteration 10): Removed `nat` from `n: nat` in `mod_exp_auto_bit_length` to address Verus type restrictions on `nat` and `int` for non-ghost code, replacing it with `usize` for executable context */
fn mod_exp_auto_bit_length(n: usize) -> (s: Vec<char>)
    ensures
        s.len() == n
{
    let mut s = Vec::new();
    for _ in 0..n {
        s.push('0');
    }
    if n > 0 {
        s[n - 1] = '1';
    }
    s
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
/* code modified by LLM (iteration 10): Fixed Verus type errors by casting `half_sy_len` and `sy.len()` to `usize` for `subrange` arguments, as `int` is disallowed in executable code context. Also added base cases for recursion. */
{
    if sy.len() == 0 {
        return vec!['1'];
    }

    if sy.len() == 1 {
        if sy[0] == '0' {
            return vec!['1'];
        } else { 
            return sx.clone();
        }
    }

    let half_sy_len: usize = sy.len() / 2;
    let half_sy_seq = sy@.subrange(0, half_sy_len as int);
    let remaining_sy_seq = sy@.subrange(half_sy_len as int, sy.len() as int);
    let half_sy_vec = half_sy_seq.to_vec();
    let remaining_sy_vec = remaining_sy_seq.to_vec();


    let half_res_vec = mod_exp(sx.clone(), half_sy_vec, sz.clone());
    let result = mod_exp(half_res_vec, remaining_sy_vec, sz);
    result
}
// </vc-code>


}

fn main() {}