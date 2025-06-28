use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to find minimum value in a multiset
fn MinOfMultiset(m: Multiset<int>) -> (min: int)
    requires
        m.len() > 0,
    ensures
        m.contains(min),
        forall|z: int| m.contains(z) ==> min <= z,
{
    // Convert multiset to sequence and find minimum
    let s = multiset_to_seq_exec(m);
    let min = find_min_in_seq(s);
    
    // Proof that min is in multiset
    proof {
        assert(s.to_multiset() =~= m);
        assert(exists|i: int| 0 <= i < s.len() && s[i] == min);
        assert(forall|z: int| m.contains(z) ==> s.to_multiset().contains(z));
        assert(forall|z: int| s.to_multiset().contains(z) ==> m.contains(z));
    }
    
    min
}

// Executable helper function to convert multiset to sequence
fn multiset_to_seq_exec(m: Multiset<int>) -> (s: Seq<int>)
    requires
        m.len() > 0,
    ensures
        s.len() == m.len(),
        s.to_multiset() =~= m,
{
    // Simple implementation: create a sequence from multiset elements
    let mut result: Seq<int> = Seq::empty();
    let ghost mut remaining = m;
    
    while remaining.len() > 0
        invariant
            remaining.len() + result.len() == m.len(),
            remaining.disjoint(result.to_multiset()),
            remaining + result.to_multiset() =~= m,
        decreases remaining.len(),
    {
        // Get an arbitrary element from the remaining multiset
        let elem = choose|x: int| remaining.contains(x);
        result = result.push(elem);
        proof {
            remaining = remaining.remove(elem);
        }
    }
    
    proof {
        assert(result.to_multiset() =~= m);
    }
    
    result
}

// Helper function to find minimum in a sequence
fn find_min_in_seq(s: Seq<int>) -> (min: int)
    requires
        s.len() > 0,
    ensures
        exists|i: int| 0 <= i < s.len() && s[i] == min,
        forall|i: int| 0 <= i < s.len() ==> min <= s[i],
{
    let mut min = s[0];
    let mut idx = 1;
    
    while idx < s.len()
        invariant
            1 <= idx <= s.len(),
            exists|i: int| 0 <= i < idx && s[i] == min,
            forall|i: int| 0 <= i < idx ==> min <= s[i],
    {
        if s[idx] < min {
            min = s[idx];
        }
        idx = idx + 1;
    }
    
    min
}

// Sort function that converts multiset to sorted sequence
fn Sort(m: Multiset<int>) -> (s: Seq<int>)
    requires
        m.len() > 0,
    ensures
        s.len() >= 0,
        s.to_multiset() =~= m,
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
{
    // Simple selection sort implementation
    let mut unsorted = multiset_to_seq_exec(m);
    let mut result: Seq<int> = Seq::empty();
    
    while unsorted.len() > 0
        invariant
            unsorted.len() + result.len() == m.len(),
            unsorted.to_multiset() + result.to_multiset() =~= m,
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q],
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < unsorted.len() ==> result[i] <= unsorted[j],
        decreases unsorted.len(),
    {
        // Find minimum in unsorted portion
        let min = find_min_in_seq(unsorted);
        let min_idx = find_index_of(unsorted, min);
        
        // Add minimum to result
        result = result.push(min);
        
        // Remove minimum from unsorted
        unsorted = unsorted.remove(min_idx);
    }
    
    result
}

// Helper function to find index of element in sequence
fn find_index_of(s: Seq<int>, elem: int) -> (idx: int)
    requires
        s.len() > 0,
        exists|i: int| 0 <= i < s.len() && s[i] == elem,
    ensures
        0 <= idx < s.len(),
        s[idx] == elem,
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s[j] != elem,
            exists|k: int| i <= k < s.len() && s[k] == elem,
    {
        if s[i] == elem {
            return i;
        }
        i = i + 1;
    }
    0  // This should never be reached due to precondition
}

// Helper spec function for sorted property
spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// Spec function version of multiset to sequence conversion
spec fn multiset_to_seq(m: Multiset<int>) -> Seq<int>
    requires
        m.len() > 0,
{
    choose|s: Seq<int>| s.len() == m.len() && s.to_multiset() =~= m
}

// Test method
fn Test(m: Multiset<int>) -> (result: (Seq<int>, int))
    requires
        m.len() > 0,
    ensures
        {
            let (s, min) = result;
            &&& s.to_multiset() =~= m
            &&& (forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q])
            &&& m.contains(min)
            &&& (forall|z: int| m.contains(z) ==> min <= z)
        }
{
    let s = Sort(m);
    let min = MinOfMultiset(m);
    
    // Proof assertions to help verification
    proof {
        assert(s.len() == m.len());
        assert(s.to_multiset() =~= m);
        assert(m.contains(min));
        assert(forall|z: int| m.contains(z) ==> min <= z);
        assert(forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]);
    }
    
    (s, min)
}

}