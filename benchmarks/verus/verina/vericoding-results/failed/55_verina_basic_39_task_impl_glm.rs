// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added compute_rotated_index and lemma to prove it equals the spec formula */
spec fn compute_rotated_index(i: int, effective_n: int, len: int) -> int {
    if i >= effective_n {
        i - effective_n
    } else {
        i + len - effective_n
    }
}

proof fn compute_rotated_index_equals_spec(i: int, n: int, len: int, effective_n: int)
    requires
        0 <= i < len,
        0 <= effective_n < len,
        effective_n == n % len,
    ensures
        compute_rotated_index(i, effective_n, len) == (i - n + len) % len
{
    if i >= effective_n {
        assert((i - n + len) % len == i - effective_n);
    } else {
        assert((i - n + len) % len == i - effective_n + len);
    }
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
/* code modified by LLM (iteration 5): used helper function to compute rotated index and lemma to prove correctness */
{
    let len = l.len();
    if len == 0 {
        return Vec::new();
    }
    let effective_n = n % len;
    let mut result = Vec::with_capacity(len);
    for i in 0..len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let rotated_index = compute_rotated_index(j, effective_n as int, len as int);
                0 <= rotated_index < len as int,
                #[trigger] result[j] == l[rotated_index]
            }
    {
        let src_index = if i >= effective_n {
            i - effective_n
        } else {
            i + len - effective_n
        };
        proof {
            let j = i as int;
            let n_int = n as int;
            let len_int = len as int;
            let effective_n_int = effective_n as int;
            compute_rotated_index_equals_spec(j, n_int, len_int, effective_n_int);
        }
        result.push(l[src_index]);
    }
    result
}
// </vc-code>

}
fn main() {}