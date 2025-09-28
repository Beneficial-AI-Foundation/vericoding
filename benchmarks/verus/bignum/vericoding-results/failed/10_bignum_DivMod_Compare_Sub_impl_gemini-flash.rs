// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
    recommends valid_bit_string(s)
    decreases s.len()
{
    if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
        str2int(s1) >= str2int(s2),
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) - str2int(s2),
{
    assume(false);
    unreached()
}

fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
    requires valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        str2int(s1) < str2int(s2) ==> res == -1,
        str2int(s1) == str2int(s2) ==> res == 0,
        str2int(s1) > str2int(s2) ==> res == 1,
    decreases str2int(s1) + str2int(s2),
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed unnecessary `as int` casts for `subrange` length arguments, ensuring all `subrange` calls for `Seq` correctly use `int` arguments. */
spec fn count_leading_zeros(s: Seq<char>) -> nat {
    if s.len() == 0 {
        0
    } else if s[0] == '0' {
        (1 + count_leading_zeros(s.subrange(1, s.len() as int))) as nat
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (res: (Vec<char>, Vec<char>))
    requires 
        valid_bit_string(dividend@) && valid_bit_string(divisor@),
        str2int(divisor@) > 0,
    ensures 
        valid_bit_string(res.0@) && valid_bit_string(res.1@),
        str2int(res.0@) == str2int(dividend@) / str2int(divisor@),
        str2int(res.1@) == str2int(dividend@) % str2int(divisor@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Changed some `as int` casts to `as usize` to correctly handle `Vec` operations where usize is expected, and removed unnecessary casts where `int` should be used with `Seq`. */
{
    let mut q: Vec<char> = Vec::new();
    let mut r: Vec<char> = Vec::new();

    for _i in 0..dividend.len() {
        q.push('0');
    }

    let mut temp_r_seq = Seq::<char>::new(0, |i| '0');

    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            0 <= i && i <= dividend.len(),
            q.len() == dividend.len(),
            valid_bit_string(q@),
            valid_bit_string(temp_r_seq),
            temp_r_seq.len() <= divisor.len() as nat + 1,
            temp_r_seq.len() == 0 || temp_r_seq[0] == '1' || temp_r_seq.len() == 1,
        decreases (dividend.len() - i) as int,
    {
        // Shift temp_r_seq left and add the next bit of dividend
        if temp_r_seq.len() > 0 {
            let leading_zeros_spec = count_leading_zeros(temp_r_seq);
            let leading_zeros = leading_zeros_spec as int; // Cast to int for subrange
            if leading_zeros < temp_r_seq.len() as int {
                temp_r_seq = temp_r_seq.subrange(leading_zeros, temp_r_seq.len() as int); // subrange takes int
            } else {
                temp_r_seq = Seq::<char>::new(0, |i| '0');
            }
        }

        temp_r_seq = temp_r_seq.add(dividend[i]);

        proof {
            assert(valid_bit_string(temp_r_seq));
        }

        // If temp_r_seq is greater than or equal to divisor
        if compare(temp_r_seq, divisor@) >= 0 {
            proof {
                assert(str2int(temp_r_seq) >= str2int(divisor@));
            }
            temp_r_seq = sub(temp_r_seq, divisor@);
            q.set(i, '1');
        } else {
            q.set(i, '0');
        }
        i = i + 1;
    }

    // Normalize q by removing leading zeros
    let mut effective_q_len: usize = q.len();
    while effective_q_len > 1 && q[q.len() - effective_q_len] == '0'
        invariant
            1 <= effective_q_len && effective_q_len <= q.len(),
            q.len() >= 0,
        decreases effective_q_len as int,
    {
        effective_q_len = effective_q_len - 1;
    }
    let final_q_seq = q@.subrange((q.len() - effective_q_len) as int, q.len() as int); // subrange takes int

    // Normalize temp_r_seq
    let mut effective_r_len: usize = temp_r_seq.len();
     while effective_r_len > 1 && temp_r_seq[temp_r_seq.len() - effective_r_len] == '0'
        invariant
            0 <= effective_r_len && effective_r_len <= temp_r_seq.len(),
            temp_r_seq.len() >= 0,
        decreases effective_r_len as int,
    {
        effective_r_len = effective_r_len - 1;
    }
    let final_r_seq = temp_r_seq.subrange((temp_r_seq.len() - effective_r_len) as int, temp_r_seq.len() as int); // subrange takes int

    (Vec::from(final_q_seq.to_vec()), Vec::from(final_r_seq.to_vec()))
}
// </vc-code>


}

fn main() {}