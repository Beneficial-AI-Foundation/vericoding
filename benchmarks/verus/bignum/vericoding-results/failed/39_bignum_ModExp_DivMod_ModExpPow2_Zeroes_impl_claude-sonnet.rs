// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
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

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        str2int(sy) == exp_int(2, n) || str2int(sy) == 0,
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
/* helper modified by LLM (iteration 10): Fixed type conversions to use ghost blocks */
proof fn bit_string_slice_valid(s: Seq<char>, start: int, end: int)
    requires valid_bit_string(s), 0 <= start <= end <= s.len()
    ensures valid_bit_string(s.subrange(start, end))
{
}

proof fn str2int_zero_property()
    ensures str2int(seq!['0']) == 0
{
}

proof fn exp_int_zero_property(x: nat)
    ensures exp_int(x, 0) == 1
{
}

proof fn exp_int_one_property(x: nat)
    ensures exp_int(x, 1) == x
{
}

proof fn mod_distributive(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures v@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant 0 <= i <= s.len(),
                  v@ == s.subrange(0, i as int)
    {
        let ghost_idx = i as int;
        v.push(s[ghost_idx]);
        i += 1;
    }
    v
}

fn vec_to_seq(v: Vec<char>) -> (s: Seq<char>)
    ensures s == v@
{
    v@
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        sy@.len() > 0 && str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed type conversions to use ghost blocks */
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    let last_idx = sy.len() - 1;
    if sy[last_idx] == '0' {
        let ghost end_idx: int = (sy@.len() - 1) as int;
        let sy_half = seq_to_vec(sy@.subrange(0, end_idx));
        let temp_res = mod_exp(sx.clone(), sy_half, sz.clone());
        let doubled = mod_exp(temp_res.clone(), vec!['1', '0'], sz.clone());
        return doubled;
    } else {
        let ghost end_idx: int = (sy@.len() - 1) as int;
        let sy_minus_one = seq_to_vec(sy@.subrange(0, end_idx));
        let temp_res = mod_exp(sx.clone(), sy_minus_one, sz.clone());
        let doubled = mod_exp(temp_res.clone(), vec!['1', '0'], sz.clone());
        let mut combined = doubled.clone();
        combined.extend(sx.iter().cloned());
        let (_, final_res) = div_mod(combined@, sz@);
        return seq_to_vec(final_res);
    }
}
// </vc-code>


}

fn main() {}