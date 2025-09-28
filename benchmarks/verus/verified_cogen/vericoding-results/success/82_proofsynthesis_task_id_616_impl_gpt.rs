// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple identity function to satisfy placeholder */
spec fn id_u32(x: u32) -> u32 { x }
// </vc-helpers>

// <vc-spec>
fn element_wise_module(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)

    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] % arr2[i]) <= i32::MAX),

    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] % arr2[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed int/usize mismatches in invariants and assertions; added decreases; implemented element-wise modulo */
    let n: usize = arr1.len();
    let mut res: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == arr1.len(),
            n == arr2.len(),
            0 <= i as int,
            i as int <= n as int,
            res.len() == i,
            res@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> res[j] == (arr1[j] % arr2[j]),
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] != 0
        decreases (n as int) - (i as int)
    {
        proof {
            assert(0 <= i as int);
            assert(i < n);
            assert(n == arr2.len());
            assert((i as int) < (n as int));
            assert((n as int) == (arr2.len() as int));
            assert((i as int) < (arr2.len() as int));
            assert(arr2[i as int] != 0);
        }
        let a: u32 = arr1[i];
        let b: u32 = arr2[i];
        let m: u32 = a % b;
        res.push(m);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}