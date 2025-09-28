// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no changes needed, helper is correct */
spec fn rotated_source_index(i: int, n: int, len: int) -> int {
    if len > 0 { (i - n + len) % len } else { 0 }
}
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: &Vec<i32>, n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> {
            let len = l.len() as int;
            let rotated_index = ((i - n as int + len) % len) as int;
            #[trigger] result[i] == l[rotated_index]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed compilation errors by using correct VST lemmas */
    let len = l.len();
    if len == 0 {
        return Vec::new();
    }
    
    let n_mod = n % len;
    let mut result = Vec::with_capacity(len);
    let mut i: usize = 0;

    while i < len
        invariant
            l.len() == len,
            result.len() == i,
            len > 0,
            n_mod == n % len,
            forall|j: int| 0 <= j < i ==> {
                let rotated_index = rotated_source_index(j, n as int, len as int);
                #[trigger] result.spec_index(j) == l.spec_index(rotated_index)
            },
        decreases len - i,
    {
        let rotated_index = (i + len - n_mod) % len;
        proof {
            let spec_rotated_index = rotated_source_index(i as int, n as int, len as int);

            let i_int = i as int;
            let n_int = n as int;
            let len_int = len as int;
            let n_mod_int = (n % len) as int;

            // Prove `(n % len) as int == n_int % len_int`
            vstd::arithmetic::div_mod::lemma_mod_of_nonneg_int(n_int, len_int);

            // Prove `(a +/- k*d) % d == a % d` to simplify expressions
            vstd::arithmetic::div_mod::lemma_mod_add_multiples(i_int - n_int, 1, len_int);

            let code_idx_term = i + len - (n % len);
            vstd::arithmetic::div_mod::lemma_mod_of_nonneg_int(code_idx_term as int, len_int);
            vstd::arithmetic::div_mod::lemma_mod_add_multiples(i_int - n_mod_int, 1, len_int);

            // Prove`(i - n) % len == (i - (n%len)) % len`
            vstd::arithmetic::div_mod::lemma_div_mod_of_nonneg(n_int, len_int);
            vstd::arithmetic::div_mod::lemma_mod_sub_multiples(i_int - n_mod_int, n_int / len_int, len_int);

            assert(rotated_index as int == spec_rotated_index);
        }
        result.push(l[rotated_index]);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}