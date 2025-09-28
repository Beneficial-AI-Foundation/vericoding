// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

proof fn max_lemma(a: nat, b: nat) 
    ensures
        max(a, b) >= a,
        max(a, b) >= b,
        max(a, b) == a || max(a, b) == b,
{
}

fn vec_index_helper(c1: &Vec<i8>, c2: &Vec<i8>, i: nat) -> (result: i8)
    requires
        i < max(c1@.len(), c2@.len()),
    ensures
        result as int == (
            if i < c1@.len() && i < c2@.len() {
                c1@[i] as int + c2@[i] as int
            } else if i < c1@.len() {
                c1@[i] as int
            } else {
                c2@[i] as int
            }
        ),
{
    /* helper modified by LLM (iteration 5): Convert sequence indexing to use nat */
    let len1 = c1@.len();
    let len2 = c2@.len();
    if i < len1 && i < len2 {
        (c1@[i] as i8 + c2@[i] as i8) as i8
    } else if i < len1 {
        c1@[i] as i8
    } else {
        c2@[i] as i8
    }
}
// </vc-helpers>

// <vc-spec>
fn hermadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==>
            result@[i] as int == (
                if i < c1@.len() && i < c2@.len() {
                    c1@[i] as int + c2@[i] as int
                } else if i < c1@.len() {
                    c1@[i] as int
                } else if i < c2@.len() {
                    c2@[i] as int
                } else {
                    0
                }
            ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix loop variable type and array indexing */
    let max_len = max(c1@.len(), c2@.len());
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < max_len as usize
        invariant
            result@.len() == i as nat,
            forall|j: nat| j < i as nat ==> result@[j] as int == (
                if j < c1@.len() && j < c2@.len() {
                    c1@[j] as int + c2@[j] as int
                } else if j < c1@.len() {
                    c1@[j] as int
                } else if j < c2@.len() {
                    c2@[j] as int
                } else {
                    0
                }
            ),
        decreases max_len - i as nat,
    {
        let value = vec_index_helper(&c1, &c2, i as nat);
        result.push(value);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}