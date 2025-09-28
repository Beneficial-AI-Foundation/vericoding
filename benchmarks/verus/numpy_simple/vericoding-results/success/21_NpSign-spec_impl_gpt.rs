// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): sign_of returns sign of an i32 with precise postconditions */
fn sign_of(x: i32) -> (r: i32)
    ensures
        (x > 0 ==> r == 1),
        (x == 0 ==> r == 0),
        (x < 0 ==> r == -1),
{
    if x > 0 {
        1
    } else if x == 0 {
        0
    } else {
        -1
    }
}
// </vc-helpers>

// <vc-spec>
fn sign(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            (a[i] > 0 ==> result[i] == 1) &&
            (a[i] == 0 ==> result[i] == 0) &&
            (a[i] < 0 ==> result[i] == -1)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix index types in asserts and add proof tying push to new element position */
    let mut result: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < a.len()
        invariant
            result.len() == k,
            0 <= k as int <= a.len(),
            forall|j: int| 0 <= j < k as int ==> {
                (a[j] > 0 ==> result[j] == 1) &&
                (a[j] == 0 ==> result[j] == 0) &&
                (a[j] < 0 ==> result[j] == -1)
            },
        decreases a.len() - k as int
    {
        let x = a[k];
        if x > 0 {
            assert(a[k as int] == x);
            let old_len: usize = result.len();
            result.push(1);
            assert(result[old_len as int] == 1);
            assert(old_len == k);
            assert(result[k as int] == 1);
        } else if x == 0 {
            assert(a[k as int] == x);
            let old_len: usize = result.len();
            result.push(0);
            assert(result[old_len as int] == 0);
            assert(old_len == k);
            assert(result[k as int] == 0);
        } else {
            assert(a[k as int] == x);
            let old_len: usize = result.len();
            result.push(-1);
            assert(result[old_len as int] == -1);
            assert(old_len == k);
            assert(result[k as int] == -1);
        }
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}