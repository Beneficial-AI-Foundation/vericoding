// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
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
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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
/* helper modified by LLM (iteration 10): Removed `mult_until_n` as it was only used in spec context and replaced with direct calculation. Removed `int2str`'s explicit `n: nat` in signature to follow Verus convention. Adjusted `int2str_spec` to use `n as nat` for recursive call to ensure correct type in spec context.*/
spec fn int2str_spec(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { Seq::singleton('0') }
    else {
        let last_bit = if n % 2 == 1 { '1' } else { '0' };
        if n / 2 == 0 { Seq::singleton(last_bit) }
        else { int2str_spec((n / 2) as nat).snoc(last_bit) }
    }
}

fn int2str(n_exec: u64) -> (result: Vec<char>)
    ensures
        int2str_spec(n_exec as nat)@ == result@,
        valid_bit_string(result@)
{
    let mut result_vec = Vec::new();
    let mut current_n: u64 = n_exec;
    if current_n == 0 {
        result_vec.push('0');
        return result_vec;
    }
    while current_n > 0
        invariant
            current_n >= 0,
            valid_bit_string(result_vec@)
        decreases current_n
    {
        if current_n % 2 == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        current_n = current_n / 2;
    }
    result_vec.reverse();
    result_vec
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
    decreases n as nat
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed `n_spec` assignment type. Removed `mult_until_n` call from `invariant` and used `exp_int(2, exponent_tracker)` as it's defined in spec context. Changed `int2str` argument to `u64`.*/
{
    let X = str2int(sx@);
    let Z = str2int(sz@);
    let Y_target = str2int(sy@);
    let n_u64 = n as u64;

    let mut result_val: nat = 1nat;
    let mut base: nat = X % Z;
    let mut exponent_power_of_2: nat = 1nat; // Represents 2^exponent_tracker
    let mut exponent_tracker: nat = 0;

    while exponent_tracker <= n_u64 as nat
        invariant
            result_val == (exp_int(X, (Y_target & (exp_int(2, exponent_tracker) - 1)) as nat)) % Z,
            base == (exp_int(X, exp_int(2, exponent_tracker))) % Z,
            exponent_power_of_2 == exp_int(2nat, exponent_tracker),
            exponent_tracker <= n_u64 as nat + 1,
            Z > 1
        decreases (n_u64 as nat + 1) - exponent_tracker
    {
        if (Y_target & exponent_power_of_2) != 0nat { // Y_target is nat, so `&` is overloaded
            result_val = (result_val * base) % Z;
        }

        if exponent_tracker < n_u64 as nat {
            base = (base * base) % Z;
            exponent_power_of_2 = exponent_power_of_2 * 2;
        }
        exponent_tracker = exponent_tracker + 1;
    }


    let res_seq = int2str(result_val as u64);
    res_seq
}
// </vc-code>


}

fn main() {}