// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added sortedness to loop invariant */
fn binary_search(a: &[i8], x: i8) -> (index: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] as int <= a[j] as int,
    ensures
        0 <= index <= a.len(),
        forall|i: int| 0 <= i < index ==> a[i] as int <= x as int,
        forall|i: int| index <= i < a.len() ==> x as int <= a[i] as int,
{
    let mut low: usize = 0;
    let mut high: usize = a.len();
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] as int <= a[j] as int,
            forall|i: int| 0 <= i < low ==> a[i] as int <= x as int,
            forall|i: int| high <= i < a.len() ==> x as int <= a[i] as int,
        decreases (high - low) as nat
    {
        let mid = low + (high - low) / 2;
        if a[mid] < x {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-helpers>

// <vc-spec>
fn numpy_searchsorted(a: Vec<i8>, v: Vec<i8>) -> (result: Vec<usize>)
    requires 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] as int <= a[j] as int,
    ensures 
        result.len() == v.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): maintained sortedness invariant */
    let mut result: Vec<usize> = Vec::with_capacity(v.len());
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            result.len() == i,
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] as int <= a[j] as int,
        decreases (v.len() - i) as nat
    {
        let idx = binary_search(&a, v[i]);
        result.push(idx);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}