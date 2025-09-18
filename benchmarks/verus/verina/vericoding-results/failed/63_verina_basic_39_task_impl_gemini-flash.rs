// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use `len()` directly in the body, which is a `usize` type that can be coerced to `nat` by Verus. */
fn len_as_nat(v: &Vec<i32>) -> (len: nat)
    ensures len == v.len()
{
    v.len()
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
/* code modified by LLM (iteration 5): Corrected `(j + len_int - n_wrapped as int)` to `(@j + len_int - n_wrapped as int)` to ensure it's treated as an `int` type in Verus. */
{
    let len_v = l.len();
    if len_v == 0 {
        return Vec::new();
    }

    let mut result: Vec<i32> = Vec::new_with_len(len_v);
    let n_wrapped = n % len_v;

    let mut i: usize = 0;
    while i < len_v
        invariant
            0 <= i && i <= len_v,
            result.len() == len_v,
            forall|j: int| 0 <= j < i ==> {
                let len_int = len_v as int;
                let rotated_index_int = (@j + len_int - n_wrapped as int) % len_int;
                #[trigger] result@[j] == l@[rotated_index_int as nat]
            },
    {
        proof {
            let len_int_for_proof = len_v as int;
            let current_l_index = (@i + len_int_for_proof - n_wrapped as int) % len_int_for_proof;
        }
        result.set(i, l[((i as int + len_v as int - n_wrapped as int) % len_v as int) as usize]);

        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}