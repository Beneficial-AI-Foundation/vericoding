// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type annotations and removed invalid lemma */
proof fn lemma_lt_transitive(x: int, y: int, z: int) 
    requires x < y, y < z
    ensures x < z
{
}

proof fn lemma_le_transitive(x: int, y: int, z: int) 
    requires x <= y, y <= z
    ensures x <= z
{
}

proof fn lemma_strict_less_than_equal(x: int, y: int)
    requires x < y
    ensures x <= y
{
}

proof fn lemma_ordering_properties(a: int, b: int)
    ensures (a <= b) && (b <= a) ==> a == b
{
}

proof fn lemma_usize_int_conversion(n: usize)
    ensures n as int == n
{
}
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i32>) -> (result: Vec<usize>)
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
/* code modified by LLM (iteration 5): Fixed vector indexing syntax */
{
    let mut result: Vec<usize> = Vec::new();
    let mut indices: Vec<usize> = (0..a.len()).collect();
    
    let mut i = 0;
    while i < indices.len()
        invariant
            0 <= i <= indices.len(),
            indices.len() == a.len(),
            forall|k: int| 0 <= k < indices.len() ==> #[trigger] indices[k] < a.len(),
            forall|k: int| 0 <= k < indices.len() ==> 0 <= indices[k] < a.len(),
    {
        result.push(indices[i]);
        i += 1;
    }

    let mut swapped = true;
    while swapped 
        invariant
            result.len() == a.len(),
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k] < a.len(),
    {
        swapped = false;
        let mut j = 0;
        while j < result.len() - 1
            invariant
                0 <= j <= result.len() - 1,
                result.len() == a.len(),
                forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k] < a.len(),
        {
            let idx1 = result[j];
            let idx2 = result[j + 1];
            if a[idx1] > a[idx2] || (a[idx1] == a[idx2] && idx1 > idx2) {
                result.swap(j, j + 1);
                swapped = true;
            }
            j += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}