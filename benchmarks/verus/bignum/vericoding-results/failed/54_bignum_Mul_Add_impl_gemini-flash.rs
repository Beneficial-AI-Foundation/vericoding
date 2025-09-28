// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed `sum_contributions` helper to simplify proof, as the multiplication logic is instead captured in the main method's loop using `final_sum_val_ghost`. */
spec fn power_of_2(exp: nat) -> nat {
    if exp == 0 { 1nat }
    else { 2nat * power_of_2(exp - 1) }
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type errors where `int` and `nat` were mixed in indexing and loop conditions by consistently casting to `usize` for array access and using `nat` for `final_sum_val_ghost` and `i`. Replaced the `sum_contributions` ghost function with direct update of `final_sum_val_ghost` within the loop invariant to simplify the proof. */
{
    let s1_len = s1.len();
    let s2_len = s2.len();

    let mut result_vec: Vec<char> = Vec::new();

    proof {
        assert forall|i: int, j: int| #![auto]
        0 <= i < s1_len && 0 <= j < s2_len
        implies s1[i] == '0' || s1[i] == '1'
        && s2[j] == '0' || s2[j] == '1'
        by { valid_bit_string(s1@); valid_bit_string(s2@); }
    }

    if s1_len == 0 || s2_len == 0 {
        if s1_len == 0 && str2int(s1@) == 0nat || s2_len == 0 && str2int(s2@) == 0nat {
            return vec!['0'];
        }
    }

    let s1_val = str2int(s1@);
    let s2_val = str2int(s2@);

    let mut final_sum_val_ghost: nat = 0nat;
    let mut i: u128 = 0;

    while i < s2_len as u128
        invariant
            0 <= i,
            i <= s2_len as u128,
            final_sum_val_ghost == (s2.subrange(0, i as nat)).map(|idx, ch| 
                if ch == '1' { str2int(s1@) * power_of_2((i as nat)-1 - idx) } else { 0nat } 
            ).fold(0nat, |acc, x| acc + x)
            // The invariant above is equivalent to the `sum_contributions` helper from previous iterations
            // and captures the current accumulated value of the product.
        decreases s2_len as u128 - i
    {
        let s2_idx = s2_len - 1 - i as usize;
        if s2[s2_idx] == '1' {
            final_sum_val_ghost = final_sum_val_ghost + s1_val * power_of_2(i as nat);
        }
        i = i + 1;
    }

    let mut n_exec: u128;
    proof {
        n_exec = final_sum_val_ghost as u128;
    }

    if n_exec == 0 {
        return vec!['0'];
    }

    while n_exec > 0
        invariant
            n_exec >= 0
        decreases n_exec
    {
        if n_exec % 2 == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        n_exec = n_exec / 2;
    }

    result_vec.reverse();
    result_vec
}
// </vc-code>


}

fn main() {}