// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): max over ints as a simple spec helper */
spec fn max_int(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

/* helper modified by LLM (iteration 3): lemma showing bounds of max_int */
proof fn lemma_max_int_bounds(a: int, b: int)
    ensures
        max_int(a, b) >= a,
        max_int(a, b) >= b,
{
    if a >= b {
        assert(max_int(a, b) == a);
    } else {
        assert(max_int(a, b) == b);
    }
}
// </vc-helpers>

// <vc-spec>
fn polyadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int + c2[i] as int
            } else if i < c1.len() && i >= c2.len() {
                result[i] as int == c1[i] as int
            } else if i >= c1.len() && i < c2.len() {
                result[i] as int == c2[i] as int
            } else {
                result[i] as int == 0
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use bounds directly from c1.len()/c2.len() and strengthen loop invariants with view lengths; add small proof steps before indexing */
    let l1: usize = c1.len();
    let l2: usize = c2.len();
    let len: usize = if l1 >= l2 { l1 } else { l2 };

    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> {
                if j < c1@.len() && j < c2@.len() {
                    result[j] as int == c1[j] as int + c2[j] as int
                } else if j < c1@.len() && j >= c2@.len() {
                    result[j] as int == c1[j] as int
                } else if j >= c1@.len() && j < c2@.len() {
                    result[j] as int == c2[j] as int
                } else {
                    result[j] as int == 0
                }
            },
        decreases len as int - i as int
    {
        let s: i8;
        if i < c1.len() && i < c2.len() {
            proof {
                assert((i as int) < (c1.len() as int));
                assert((i as int) < (c2.len() as int));
                assert((c1.len() as int) == c1@.len());
                assert((c2.len() as int) == c2@.len());
            }
            let a: i8 = c1[i];
            let b: i8 = c2[i];
            s = a + b;
        } else if i < c1.len() {
            proof {
                assert((i as int) < (c1.len() as int));
                assert((c1.len() as int) == c1@.len());
            }
            s = c1[i];
        } else if i < c2.len() {
            proof {
                assert((i as int) < (c2.len() as int));
                assert((c2.len() as int) == c2@.len());
            }
            s = c2[i];
        } else {
            s = 0i8;
        }
        result.push(s);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}