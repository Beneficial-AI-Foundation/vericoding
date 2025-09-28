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
/* helper modified by LLM (iteration 10): Fixed nat/int conversion issues in proof function */
proof fn mod_exp_rec(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
    requires
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        sy.len() > 0 && str2int(sz) > 1
    ensures
        valid_bit_string(res),
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
    decreases sy.len()
{
    let sy_len: nat = sy.len();
    
    if sy_len == 0 {
        seq!['1']
    } else {
        let last_index: nat = sy_len - 1;
        let last_char: char = sy[last_index];
        let pre_sy: Seq<char> = sy.subrange(0, last_index as int);
        
        let res1: Seq<char> = mod_exp_rec(sx, pre_sy, sz);
        let res_sq: Seq<char> = add(res1, res1);
        let res_sq_mod: Seq<char> = div_mod(res_sq, sz).1;
        
        if last_char == '0' {
            res_sq_mod
        } else {
            let res_times_sx: Seq<char> = add(res_sq_mod, sx);
            div_mod(res_times_sx, sz).1
        }
    }
}
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
    /* code modified by LLM (iteration 10): Fixed nat/int conversion issues in executable code */
    let sy_len: usize = sy.len();
    
    if sy_len == 0 {
        seq!['1']
    } else {
        let last_index: usize = sy_len - 1;
        let last_char: char = sy[last_index];
        let pre_sy: Seq<char> = sy.subrange(0, last_index as int);
        
        let res1: Seq<char> = mod_exp(sx, pre_sy, sz);
        let res_sq: Seq<char> = add(res1, res1);
        let res_sq_mod: Seq<char> = div_mod(res_sq, sz).1;
        
        if last_char == '0' {
            res_sq_mod
        } else {
            let res_times_sx: Seq<char> = add(res_sq_mod, sx);
            div_mod(res_times_sx, sz).1
        }
    }
}
// </vc-code>


}

fn main() {}