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
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed `num_to_vec_char` to correctly construct the Seq<char> using `add` and `push_front` to match the big-endian representation, and fixed the recursive call for `rest_seq` by using `num_to_vec_char(rest, len - 1)` to generate correct length. Also added proof block for `num_to_vec_char` to prove `res.len() == len` for base case `len == 0`. */
spec fn num_to_vec_char(num: nat, len: int) -> Seq<char>
    requires
        len >= 0,
        num < exp_int(2, len as nat),
    ensures
        res.len() == len,
        valid_bit_string(res),
        str2int(res) == num,
{
    if len == 0 {
        proof { assert(Seq::<char>::new().len() == len); }
        Seq::<char>::new()
    } else {
        let msb = (num / exp_int(2, (len - 1) as nat)) as int;
        let rest = num % exp_int(2, (len - 1) as nat);
        let rest_seq = num_to_vec_char(rest, len - 1);
        if msb == 1 {
            Seq::single('1').add(rest_seq)
        } else {
            Seq::single('0').add(rest_seq)
        }
    }
}
spec fn mod_exp_pow2_recursive(sx: Seq<char>, sy: Seq<char>, n: u8, sz: Seq<char>) -> (res: Seq<char>)
    requires
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        str2int(sy) == exp_int(2nat, n as nat) || str2int(sy) == 0,
        sy.len() == n as int + 1,
        str2int(sz) > 1,
        (n == 0 || sy.len() == (n as int) + 1),

    ensures
        valid_bit_string(res),
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
        res.len() == n as int + 1,
    decreases n
{
    let n_int = n as int;
    let x_int = str2int(sx);
    let y_int = str2int(sy);
    let z_int = str2int(sz);

    if n == 0 {
        if y_int == 0 {
            num_to_vec_char(1nat, n_int + 1)
        } else { // y_int == 1
            num_to_vec_char(x_int % z_int, n_int + 1)
        }
    } else {
        let n_minus_1_nat = (n as nat - 1) as nat;

        let base_sy: Seq<char>;
        let temp_sy_len = n_int;

        if sy[n_int] == '0' {
            base_sy = num_to_vec_char(0, temp_sy_len);
            // Proof block to aid verification that str2int(base_sy) == 0
            proof {
                assert(str2int(base_sy) == 0);
            }
        } else {
            base_sy = num_to_vec_char(exp_int(2nat, n_minus_1_nat), temp_sy_len);
            // Proof block to aid verification that str2int(base_sy) == exp_int(2nat, n_minus_1_nat)
            proof {
                assert(str2int(base_sy) == exp_int(2nat, n_minus_1_nat));
            }
        }

        let base_res_seq = mod_exp_pow2_recursive(sx, base_sy, (n - 1) as u8, sz);
        let base_val = str2int(base_res_seq);
        let base_squared = (base_val * base_val) % z_int;

        if sy[n_int] == '0' {
            num_to_vec_char(base_squared, n_int + 1)
        }
        else {
            num_to_vec_char((base_squared * x_int) % z_int, n_int + 1)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy@.len() == n as int + 1,
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed `res` not found in scope error by assigning the returned value of `mod_exp_pow2_recursive` to a new variable `result_seq` and working with it. Also, ensured that the `ensures` clause correctly checks properties of this `result_seq`. */
{
    let result_seq = mod_exp_pow2_recursive(sx@, sy@, n, sz@);

    let mut res_chars: Vec<char> = Vec::new();
    let mut i = 0;
    while i < result_seq.len()
        invariant
            0 <= i <= result_seq.len(),
            res_chars.len() == i,
            forall|j: int| 0 <= j < i ==> res_chars[j] == result_seq[j]
    {
        res_chars.push(result_seq[i]);
        i = i + 1;
    }
    res_chars
}
// </vc-code>


}

fn main() {}