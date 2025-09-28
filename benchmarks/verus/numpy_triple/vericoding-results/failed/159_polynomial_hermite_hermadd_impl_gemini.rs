// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [retained helper to model spec] */
spec fn summed_val(c1: Seq<i8>, c2: Seq<i8>, i: int) -> int {
    if i < c1.len() && i < c2.len() {
        c1[i] as int + c2[i] as int
    } else if i < c1.len() {
        c1[i] as int
    } else if i < c2.len() {
        c2[i] as int
    } else {
        0
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
    /* code modified by LLM (iteration 2): [removed unsupported capacity() from invariant] */
    let n1 = c1.len();
    let n2 = c2.len();
    let n_max = if n1 >= n2 { n1 } else { n2 };

    let mut result: Vec<i8> = Vec::with_capacity(n_max);
    let mut i: usize = 0;

    while i < n_max
        invariant
            0 <= i <= n_max,
            n1 == c1@.len(),
            n2 == c2@.len(),
            n_max == if n1 >= n2 { n1 } else { n2 },
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == summed_val(c1@, c2@, j),
        decreases n_max - i
    {
        let val = if i < n1 && i < n2 {
            c1[i] + c2[i]
        } else if i < n1 {
            c1[i]
        } else {
            proof {
                if n1 >= n2 {
                    assert(i >= n1);
                    assert(i < n_max);
                    assert(n_max == n1);
                    assert(i < n1);
                    assert(false);
                }
                assert(i < n2);
            }
            c2[i]
        };
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}