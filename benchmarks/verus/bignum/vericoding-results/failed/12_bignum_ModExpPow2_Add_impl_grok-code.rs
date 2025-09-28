// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
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
// </vc-preamble>

// <vc-helpers>
fn nat_to_vec(n: nat) -> Vec<char>
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        let mut temp = n;
        let mut v = Vec::new();
        while temp > 0
            invariant
                temp > 0,
            decreases temp
        {
            let bit = if temp % 2 == 1 { '1' } else { '0' };
            v.push(bit);
            temp = temp / 2;
        }
        v.reverse();
        v
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
        (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
        sy@.len() == n as int + 1 &&
        str2int(sz@) > 1
    ensures 
        valid_bit_string(res@) &&
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases n
// </vc-spec>
// <vc-code>
{
    let ghost base = str2int(sx@);
    let ghost mod_ = str2int(sz@);
    let ghost val = if n == 0 {
        if sy@[0] == '0' { 0 } else { base % mod_ }
    } else {
        let ghost prev_val = exp_int(base, exp_int(2nat, (n - 1) as nat));
        (prev_val * prev_val) % mod_
    };
    res = nat_to_vec(val);
}
// </vc-code>


}

fn main() {}