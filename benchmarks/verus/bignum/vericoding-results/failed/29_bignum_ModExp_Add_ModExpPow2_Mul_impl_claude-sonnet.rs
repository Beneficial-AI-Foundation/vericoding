// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
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

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
        (str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0) &&
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

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) * str2int(s2)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type annotations and function signatures */
spec fn mod_op(a: nat, b: nat) -> nat
{
    a % b
}

proof fn mod_exp_base_case(x: nat, z: nat)
    requires z > 1
    ensures exp_int(x, 0) % z == 1nat % z
{
}

proof fn mod_exp_inductive_step(x: nat, y: nat, z: nat)
    requires z > 1, y > 0
    ensures exp_int(x, y) % z == (x * exp_int(x, (y - 1) as nat)) % z
{
}

proof fn mod_distributive(a: nat, b: nat, m: nat)
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
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
    /* code modified by LLM (iteration 10): Fixed nat/int type usage in executable code */
    if sy.len() == 1 && sy[0] == '0' {
        seq!['1']
    } else {
        let half_len = sy.len() - 1;
        let half_exp = mod_exp(sx, sy.subrange(0, half_len as int), sz);
        let squared = mul(half_exp, half_exp);
        let last_idx = sy.len() - 1;
        if sy[last_idx as int] == '1' {
            mul(squared, sx)
        } else {
            squared
        }
    }
}
// </vc-code>


}

fn main() {}