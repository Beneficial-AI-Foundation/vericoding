// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by replacing membership quantifiers with exists to fix syntax */
spec
fn is_sorted(s: Seq<usize>) -> bool
{
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

fn insertion_sort(v: Vec<usize>) -> (result: Vec<usize>)
    requires
        true,
    ensures
        is_sorted(result@),
        forall|x: usize| exists|i: int| 0 <= i < v.len() && v@[i] == x <==> exists|j: int| 0 <= j < result.len() && result@[j] == x,
{
    if v.len() == 0 {
        return v;
    }
    let mut arr = v;
    let mut i = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            is_sorted(arr@.subrange(0, i as int)),
            forall|k: int| 0 <= k < arr.len() ==> arr@[k] == v@[k],
            forall|x: usize| exists|i1: int| 0 <= i1 < v.len() && v@[i1] == x <==> exists|j1: int| 0 <= j1 < arr.len() && arr@[j1] == x,
        decreases arr.len() - i,
    {
        let mut j = i;
        let key = arr@[j];
        while j > 0 && arr@[j - 1] > key
            invariant
                0 <= j <= i,
                is_sorted(arr@.subrange(0, j + 1)),
                forall|k: int| 0 <= k < arr.len() && k != j ==> arr@[k] == v@[k],
            decreases j,
        {
            arr.set(j, arr@[j - 1]);
            j = j - 1;
        }
        arr.set(j, key);
        i = i + 1;
    }
    arr
}
// </vc-helpers>

// <vc-spec>
fn nonzero(a: Vec<f32>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] < a.len() && a[indices[i] as int] != 0.0f32),
        forall|j: int| 0 <= j < a.len() ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by declaring i as usize */
{
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            indices.len() <= i,
            forall|k: int| 0 <= k < indices.len() ==> (indices@[k] < a.len() && a@[indices@[k] as int] != 0.0f32),
            forall|j: int| 0 <= j < i ==> (a@[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices@[k] == j),
        decreases a.len() - i,
    {
        if a@[i] != 0.0f32 {
            indices.push(i);
        }
        i = i + 1;
    }
    let sorted_indices = insertion_sort(indices);
    sorted_indices
}
// </vc-code>

}
fn main() {}