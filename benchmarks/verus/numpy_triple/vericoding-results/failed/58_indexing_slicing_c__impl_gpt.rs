// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct a 2-element vector pair */
fn make_pair_vec(x: i8, y: i8) -> (v: Vec<i8>)
    ensures
        v.len() == 2,
        v@.len() == 2,
        v[0] == x,
        v[1] == y,
{
    let mut v: Vec<i8> = Vec::new();
    v.push(x);
    v.push(y);
    v
}
// </vc-helpers>

// <vc-spec>
fn c_(arr1: Vec<i8>, arr2: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires arr1.len() == arr2.len(),
    ensures 
        result.len() == arr1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i]@.len() == 2 &&
            result[i][0] == arr1[i] &&
            result[i][1] == arr2[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement zip with precise forall proof using implies and push postcondition */
    let n = arr1.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            n == arr1.len(),
            n == arr2.len(),
            forall|j: int| 0 <= j < i as int ==>
                result[j]@.len() == 2 &&
                result[j][0] == arr1[j] &&
                result[j][1] == arr2[j],
        decreases n - i
    {
        let x = arr1[i];
        let y = arr2[i];
        let inner = make_pair_vec(x, y);

        let old_len = result.len();
        result.push(inner);

        proof {
            let old_len_i: int = old_len as int;
            assert forall|j: int|
                implies(0 <= j && j < old_len_i + 1,
                    result[j]@.len() == 2 &&
                    result[j][0] == arr1[j] &&
                    result[j][1] == arr2[j]
                )
            by
            {
                if j < old_len_i {
                    // From the invariant for previous elements
                } else {
                    // Now j >= old_len_i and j < old_len_i + 1, hence j == old_len_i
                    assert(old_len_i <= j);
                    assert(j < old_len_i + 1);
                    assert(j <= old_len_i);
                    assert(j == old_len_i);

                    // From push, the newly appended element is at index old_len_i
                    assert(result[old_len_i] == inner);

                    // Relate the new element to x and y
                    assert(inner[0] == x);
                    assert(inner[1] == y);

                    let i_i: int = i as int;
                    assert(old_len_i == i_i);

                    // Conclude the required properties
                    assert(result[j]@.len() == 2);
                    assert(result[j][0] == inner[0]);
                    assert(result[j][1] == inner[1]);
                    assert(x == arr1[i_i]);
                    assert(y == arr2[i_i]);
                    assert(result[j][0] == arr1[j]);
                    assert(result[j][1] == arr2[j]);
                }
            }
        }

        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}