// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [brief description] */
fn max_len(a: usize, b: usize) -> usize { if a >= b { a } else { b } }
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
/* code modified by LLM (iteration 5): Corrected `c1.view()@[j]` to `c1@[j]` and `c2.view()@[j]` to `c2@[j]` since `c1` and `c2` are already `Seq` types when accessed in the `forall` quantifier. Removed redundant `view()` calls on `c1` and `c2` inside the loop body as well.*/
{
    let len1 = c1.len();
    let len2 = c2.len();
    let result_len = max_len(len1, len2);
    let mut result: Vec<i8> = Vec::with_capacity(result_len);
    let mut i: usize = 0;

    while i < result_len
        invariant
            result.len() == i,
            i <= result_len,
            forall|j: int| 0 <= j < i ==> {
                if j < len1 && j < len2 {
                    result@[j] as int == c1@[j] as int + c2@[j] as int
                } else if j < len1 {
                    result@[j] as int == c1@[j] as int
                } else if j < len2 {
                    result@[j] as int == c2@[j] as int
                } else {
                    result@[j] as int == 0
                }
            }
        decreases result_len - i
    {
        let mut term1: i8 = 0;
        let mut term2: i8 = 0;

        if i < len1 {
            term1 = c1@[i];
        }
        if i < len2 {
            term2 = c2@[i];
        }

        proof {
            if i < len1 && i < len2 {
                assert(term1 as int == c1@[i] as int);
                assert(term2 as int == c2@[i] as int);
            } else if i < len1 {
                assert(term1 as int == c1@[i] as int);
                assert(term2 as int == 0);
            } else if i < len2 {
                assert(term1 as int == 0);
                assert(term2 as int == c2@[i] as int);
            } else {
                assert(term1 as int == 0);
                assert(term2 as int == 0);
            }
        }

        result.push(term1.checked_add(term2).unwrap());
        i = i.checked_add(1).unwrap();
    }
    result
}
// </vc-code>


}
fn main() {}