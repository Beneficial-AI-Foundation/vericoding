// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermmul(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures

        (c1.len() == 0 || c2.len() == 0) ==> (result.len() == 1 && result[0] == 0),

        (c1.len() > 0 && c2.len() > 0) ==> result.len() == c1.len() + c2.len() - 1,

        (c2.len() == 1 && c1.len() > 0) ==>
            forall|i: int| 0 <= i < c1.len() ==> result[i] == c1[i] * c2[0],
        (c1.len() == 1 && c2.len() > 0) ==>
            forall|i: int| 0 <= i < c2.len() ==> result[i] == c2[i] * c1[0],

        ((forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || 
         (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0)) ==>
            forall|k: int| 0 <= k < result.len() ==> result[k] == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed indexing and arithmetic errors by adding proof blocks and explicit bounds */
    {
        let n = c1.len();
        let m = c2.len();

        if n == 0 || m == 0 {
            let mut zero_vec = Vec::new();
            zero_vec.push(0);
            return zero_vec;
        }

        proof {
            assert(n >= 1 && m >= 1);
        }

        let len = n + m - 1;
        proof {
            assert(len >= 1);
        }

        let mut result = Vec::new();
        for _ in 0..len {
            result.push(0);
        }

        if m == 1 {
            proof {
                assert(len == n);
            }
            for i in 0..n {
                result[i] = c1[i] * c2[0];
            }
            proof {
                assert(forall|i: int| 0 <= i < n ==> result[i] == c1[i] * c2[0]);
            }
            return result;
        }

        if n == 1 {
            proof {
                assert(len == m);
            }
            for i in 0..m {
                result[i] = c2[i] * c1[0];
            }
            proof {
                assert(forall|i: int| 0 <= i < m ==> result[i] == c2[i] * c1[0]);
            }
            return result;
        }

        for i in 0..n {
            for j in 0..m {
                let idx = i + j;
                proof {
                    assert(idx < len);
                }
                let temp = result[idx];
                result[idx] = temp + c1[i] * c2[j];
            }
        }

        result
    }
// </vc-code>

}
fn main() {}