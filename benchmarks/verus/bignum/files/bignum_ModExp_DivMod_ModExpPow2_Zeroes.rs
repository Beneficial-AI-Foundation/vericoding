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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}