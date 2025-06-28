use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to get the k-th smallest element from two sorted arrays
fn find_kth_element(a: &Vec<int>, b: &Vec<int>, k: usize) -> (result: int)
    requires
        a.len() > 0 || b.len() > 0,
        k < a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= a[i + 1],
        forall|i: int| 0 <= i < b.len() - 1 ==> b[i] <= b[i + 1],
    ensures
        // The result is the k-th smallest element when merging a and b
        exists|merged: Seq<int>| is_merged_sorted(a@, b@, merged) && result == merged[k as int]
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut count: usize = 0;
    let mut current: int = 0;

    while count <= k
        invariant
            i <= a.len(),
            j <= b.len(),
            count <= k + 1,
            i + j == count,
            // Ensure we can safely access array elements
            (i < a.len() || j < b.len() || count > k),
    {
        if i >= a.len() {
            current = b[j];
            j += 1;
        } else if j >= b.len() {
            current = a[i];
            i += 1;
        } else if a[i] <= b[j] {
            current = a[i];
            i += 1;
        } else {
            current = b[j];
            j += 1;
        }
        
        if count == k {
            return current;
        }
        count += 1;
    }
    
    current
}

// Specification function to check if a sequence is the sorted merge of two sequences
spec fn is_merged_sorted(a: Seq<int>, b: Seq<int>, merged: Seq<int>) -> bool {
    merged.len() == a.len() + b.len() &&
    (forall|i: int| 0 <= i < merged.len() - 1 ==> merged[i] <= merged[i + 1]) &&
    // Use multiset equality to handle duplicates properly
    merged.to_multiset() == a.to_multiset().add(b.to_multiset())
}

fn FindMedian(a: Vec<int>, b: Vec<int>) -> (median: int)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= a[i + 1],
        forall|i: int| 0 <= i < b.len() - 1 ==> b[i] <= b[i + 1]
    ensures
        // For even total length (which is always the case since a.len() == b.len()), 
        // median is average of two middle elements
        median == (find_kth_element(&a, &b, a.len() - 1) + find_kth_element(&a, &b, a.len())) / 2
{
    let total_len = a.len() + b.len();
    
    // Since a.len() == b.len(), total_len is always even
    // Return average of two middle elements
    let left_median = find_kth_element(&a, &b, total_len / 2 - 1);
    let right_median = find_kth_element(&a, &b, total_len / 2);
    (left_median + right_median) / 2
}

}