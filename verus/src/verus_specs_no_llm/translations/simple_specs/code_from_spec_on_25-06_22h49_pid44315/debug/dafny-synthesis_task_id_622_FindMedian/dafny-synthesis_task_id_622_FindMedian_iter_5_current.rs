use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Specification function to check if a sequence is the sorted merge of two sequences
spec fn is_merged_sorted(a: Seq<int>, b: Seq<int>, merged: Seq<int>) -> bool {
    merged.len() == a.len() + b.len() &&
    (forall|i: int| 0 <= i < merged.len() - 1 ==> merged[i] <= merged[i + 1]) &&
    // Use multiset equality to handle duplicates properly
    merged.to_multiset() == a.to_multiset().add(b.to_multiset())
}

// Helper spec function to merge two sorted sequences
spec fn merge_sequences(a: Seq<int>, b: Seq<int>) -> Seq<int>
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] <= b[0] {
        seq![a[0]] + merge_sequences(a.subrange(1, a.len() as int), b)
    } else {
        seq![b[0]] + merge_sequences(a, b.subrange(1, b.len() as int))
    }
}

// Helper spec function to define what the k-th element should be
spec fn kth_element_in_merged(a: Seq<int>, b: Seq<int>, k: int) -> int
    recommends
        0 <= k < a.len() + b.len()
{
    let merged = merge_sequences(a, b);
    merged[k]
}

// Helper lemma to prove properties about merged sequences
proof fn lemma_merge_preserves_order(a: Seq<int>, b: Seq<int>)
    requires
        forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= a[i + 1],
        forall|i: int| 0 <= i < b.len() - 1 ==> b[i] <= b[i + 1],
    ensures
        is_merged_sorted(a, b, merge_sequences(a, b))
    decreases a.len() + b.len()
{
    if a.len() == 0 || b.len() == 0 {
        // Base cases are trivial
    } else {
        if a[0] <= b[0] {
            lemma_merge_preserves_order(a.subrange(1, a.len() as int), b);
        } else {
            lemma_merge_preserves_order(a, b.subrange(1, b.len() as int));
        }
    }
}

// Helper function to get the k-th smallest element from two sorted arrays
fn find_kth_element(a: &Vec<int>, b: &Vec<int>, k: usize) -> (result: int)
    requires
        a.len() > 0 || b.len() > 0,
        k < a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= a[i + 1],
        forall|i: int| 0 <= i < b.len() - 1 ==> b[i] <= b[i + 1],
    ensures
        result == kth_element_in_merged(a@, b@, k as int)
{
    proof {
        lemma_merge_preserves_order(a@, b@);
    }
    
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut count: usize = 0;
    let mut current: int = 0;

    while count <= k
        invariant
            i <= a.len(),
            j <= b.len(),
            i + j == count,
            count <= k + 1,
            // If we haven't reached k yet, we can make progress
            count <= k ==> (i < a.len() || j < b.len()),
            // The current value represents the (count-1)th element if count > 0
            count > 0 ==> {
                let taken_from_a = a@.subrange(0, i as int);
                let taken_from_b = b@.subrange(0, j as int);
                let merged_taken = merge_sequences(taken_from_a, taken_from_b);
                merged_taken.len() == count &&
                (count > 0 ==> current == merged_taken[count as int - 1])
            }
    {
        if i >= a.len() {
            // Only elements from b remain
            current = b[j];
            j += 1;
        } else if j >= b.len() {
            // Only elements from a remain  
            current = a[i];
            i += 1;
        } else if a[i] <= b[j] {
            // Take from a
            current = a[i];
            i += 1;
        } else {
            // Take from b
            current = b[j];
            j += 1;
        }
        
        count += 1;
        
        if count > k {
            break;
        }
    }
    
    current
}

fn FindMedian(a: Vec<int>, b: Vec<int>) -> (median: int)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= a[i + 1],
        forall|i: int| 0 <= i < b.len() - 1 ==> b[i] <= b[i + 1]
    ensures
        // For even total length, median is average of two middle elements
        median == (kth_element_in_merged(a@, b@, (a.len() - 1) as int) + 
                  kth_element_in_merged(a@, b@, a.len() as int)) / 2
{
    let total_len = a.len() + b.len();
    
    // Since a.len() == b.len(), total_len is always even
    // Return average of two middle elements
    let left_median = find_kth_element(&a, &b, total_len / 2 - 1);
    let right_median = find_kth_element(&a, &b, total_len / 2);
    (left_median + right_median) / 2
}

}