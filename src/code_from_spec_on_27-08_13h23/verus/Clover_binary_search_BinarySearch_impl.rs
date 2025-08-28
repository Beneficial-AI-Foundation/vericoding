use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_midpoint(low: int, high: int)
    requires
        low <= high,
    ensures
        low <= (low + high) / 2 <= high,
{
    // This lemma is straightforward as it follows from integer arithmetic
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn binary_search(a: &[i32], key: i32) -> (n: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    ensures 
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> a[i] < key,
        n == a.len() ==> forall|i: int| 0 <= i < a.len() ==> a[i] < key,
        forall|i: int| n <= i < a.len() ==> a[i] >= key
// </vc-spec>
// </vc-spec>

// <vc-code>
fn binary_search(a: &[i32], key: i32) -> (n: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    ensures 
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> a[i] < key,
        n == a.len() ==> forall|i: int| 0 <= i < a.len() ==> a[i] < key,
        forall|i: int| n <= i < a.len() ==> a[i] >= key
{
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int| 0 <= i < low ==> a[i] < key,
            forall|i: int| high <= i < a.len() ==> a[i] >= key
    {
        let mid: usize = (low + high) / 2;
        proof {
            lemma_midpoint(low as int, high as int);
        }
        if a[mid] < key {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-code>

fn main() {}

}