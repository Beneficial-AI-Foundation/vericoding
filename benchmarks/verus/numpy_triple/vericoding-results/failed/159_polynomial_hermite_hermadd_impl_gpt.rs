// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): keep simple max helper and its basic properties lemma */
pub open spec fn max_int(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub proof fn max_int_props(a: int, b: int)
    ensures
        max_int(a, b) >= a,
        max_int(a, b) >= b,
        (a >= b ==> max_int(a, b) == a),
        (b > a ==> max_int(a, b) == b),
{
    if a >= b {
        assert(max_int(a, b) == a);
    } else {
        assert(b > a);
        assert(max_int(a, b) == b);
    }
    assert(max_int(a, b) >= a);
    assert(max_int(a, b) >= b);
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
    /* code modified by LLM (iteration 5): implement element-wise addition with a strengthening proof to satisfy the loop invariant */
    let n1: usize = c1.len();
    let n2: usize = c2.len();
    let m: usize = if n1 >= n2 { n1 } else { n2 };

    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            res@.len() == i as int,
            n1 as int == c1@.len(),
            n2 as int == c2@.len(),
            0 <= i as int <= m as int,
            forall|j: int| 0 <= j < i as int ==> res@[j] as int == (
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
        decreases m as int - i as int
    {
        let val: i8;
        if i < n1 && i < n2 {
            let a = c1[i];
            let b = c2[i];
            val = a + b;
        } else if i < n1 {
            val = c1[i];
        } else if i < n2 {
            val = c2[i];
        } else {
            val = 0i8;
        }
        res.push(val);

        // Prove the invariant clause for the newly appended index
        proof {
            let j = i as int;
            assert(0 <= j);
            assert(res@[j] == val);
            if i < n1 && i < n2 {
                // Bridge exec indexing with spec views
                assert(c1@[j] == c1[i]);
                assert(c2@[j] == c2[i]);
                assert(res@[j] as int == (c1@[j] as int + c2@[j] as int));
            } else if i < n1 {
                assert(c1@[j] == c1[i]);
                assert(res@[j] as int == c1@[j] as int);
            } else if i < n2 {
                assert(c2@[j] == c2[i]);
                assert(res@[j] as int == c2@[j] as int);
            } else {
                assert(res@[j] as int == 0);
            }
        }

        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}