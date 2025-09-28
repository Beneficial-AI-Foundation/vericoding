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
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
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
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) + str2int(s2)
{
    assume(false);
    unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor) &&
        str2int(divisor) > 0
    ensures 
        valid_bit_string(res.0) && valid_bit_string(res.1) &&
        str2int(res.0) == str2int(dividend) / str2int(divisor) &&
        str2int(res.1) == str2int(dividend) % str2int(divisor)
{
    assume(false);
    unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
        (str2int(sy) == exp_int(2, n) || str2int(sy) == 0) &&
        sy.len() == n + 1 &&
        str2int(sz) > 1
    ensures 
        valid_bit_string(res) &&
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
    decreases n
{
    assume(false);
    unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
    ensures 
        s.len() == n &&
        valid_bit_string(s) &&
        str2int(s) == 0 &&
        all_zero(s)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
        sy.len() > 0 && str2int(sz) > 1
    ensures 
        valid_bit_string(res) &&
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
    decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed type conversion - use usize for indexing and slicing */
    if sy.len() == 1 {
        if sy.index(0) == '0' {
            let result = zeros(1nat);
            proof {
                assert(result.index(0int) == '0');
                assert(str2int(result) == 0);
                assert(exp_int(str2int(sx), 0) == 1);
                assert(1 % str2int(sz) == 1);
            }
            let one = seq!['1'];
            return one;
        } else {
            let result = div_mod(sx, sz).1;
            return result;
        }
    } else {
        let last_idx: usize = sy.len() - 1;
        let last_bit = sy.index(last_idx);
        let sy_shifted = sy.subrange(0, last_idx);
        let rec_result = mod_exp(sx, sy_shifted, sz);
        let squared = div_mod(add(rec_result, rec_result), sz).1;
        
        if last_bit == '1' {
            let multiplied = div_mod(add(squared, sx), sz).1;
            return multiplied;
        } else {
            return squared;
        }
    }
}
// </vc-code>


}

fn main() {}