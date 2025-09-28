// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed */
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed index access with as int, added proof asserts to trigger postconditions */
    let mut result: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> 
                a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],
            forall|i: int, j: int| 0 <= i < j < result.len() && 
                a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
                result[i] < result[j]
        decreases a.len() - i
    {
        let val = i;
        let mut pos = 0;
        while pos < result.len() && a[(result[pos] as int)] <= a[(val as int)]
            invariant
                0 <= pos <= result.len(),
                result.len() == i,
                i < a.len()
            decreases result.len() - pos
        {
            pos += 1;
        }
        result.insert(pos, val);
        proof {
            assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> 
                a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int]);
            assert(forall|i: int, j: int| 0 <= i < j < result.len() && 
                a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
                result[i] < result[j]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}