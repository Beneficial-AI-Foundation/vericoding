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
    recommends valid_bit_string(s)
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
        valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) + str2int(s2),
{
    assume(false);
    unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor) &&
        str2int(divisor) > 0,
    ensures 
        valid_bit_string(res.0) && valid_bit_string(res.1) &&
        str2int(res.0) == str2int(dividend) / str2int(divisor) &&
        str2int(res.1) == str2int(dividend) % str2int(divisor),
{
    assume(false);
    unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) * str2int(s2),
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Replaced `Seq::from_str` with `Seq::from` to fix compilation errors */
spec fn mod_exp_pow2_recursive(sx: Seq<char>, sy: Seq<char>, n: u8, sz: Seq<char>) -> Seq<char>
    recommends
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
        sy.len() == (n as int + 1) && (str2int(sy) == exp_int(2nat, n as nat) || str2int(sy) == 0) &&
        str2int(sz) > 1,
    ensures
        valid_bit_string(mod_exp_pow2_recursive(sx, sy, n, sz)) &&
        str2int(mod_exp_pow2_recursive(sx, sy, n, sz)) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
    decreases n
{
    if n == 0 {
        if sy[0] == '1' {
            div_mod(sx, sz).1
        } else {
            Seq::from('0')
        }
    } else {
        let (half_y, _) = div_mod(sy, Seq::from('1').add(Seq::from('0'))); // sy / 2
        let result_half = mod_exp_pow2_recursive(sx, half_y, (n-1) as u8, sz);

        let result_squared = mul(result_half, result_half);
        let (temp_res_squared, _) = div_mod(result_squared, sz);

        if sy[n as int] == '1' {
            let result_final = mul(temp_res_squared, sx);
            div_mod(result_final, sz).1
        } else {
            div_mod(temp_res_squared, sz).1
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
        (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
        sy@.len() == n as int + 1 &&
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@) &&
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Ensured 'i' is an integer, matching 'result_seq.len()' to fix type mismatch */
{
    let sy_seq = sy@;
    let sx_seq = sx@;
    let sz_seq = sz@;

    proof {
        if n == 0 {
            assert(sy_seq.len() == 1);
            assert(str2int(sy_seq) == exp_int(2nat, 0nat) || str2int(sy_seq) == 0nat);
        }
    }

    let result_seq = mod_exp_pow2_recursive(sx_seq, sy_seq, n, sz_seq);

    let mut result_vec: Vec<char> = Vec::new();
    let mut i: int = 0; // Changed type to int explicitely
    while i < result_seq.len() // 'len()' returns 'int'
        invariant 
            result_seq.len() >= 0,
            i <= result_seq.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == result_seq.index(j)
    {
        result_vec.push(result_seq.index(i));
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}

fn main() {}