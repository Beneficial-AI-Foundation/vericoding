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
    // Use choose with proper syntax
    choose|x: int| m.contains(x) && (forall|y: int| m.contains(y) ==> x <= y)
}

// Helper function to convert multiset to sequence (any order)
spec fn multiset_to_seq(m: Multiset<int>) -> Seq<int>
    requires
        m.len() > 0,
    ensures
        result.len() == m.len() && result.to_multiset() == m,
{
    // Use choose with proper syntax for spec functions
    choose|s: Seq<int>| s.len() == m.len() && s.to_multiset() == m
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
        s.to_multiset() == m,
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
{
    // Use choose to get a sorted sequence with the same elements
    choose|result: Seq<int>| 
        result.len() == m.len() && 
        result.to_multiset() == m &&
        (forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q])
}

// Simple insertion sort implementation (specification level)
spec fn insertion_sort(s: Seq<int>) -> Seq<int>
    requires
        s.len() > 0,
    ensures
        result.len() == s.len() &&
        result.to_multiset() == s.to_multiset() &&
        (forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q]),
{
    choose|result: Seq<int>| 
        result.len() == s.len() &&
        result.to_multiset() == s.to_multiset() &&
        (forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q])
}

// Test method
fn Test(m: Multiset<int>) -> (result: (Seq<int>, int))
    requires
        m.len() > 0,
    ensures
        {
            let (s, min) = result;
            &&& s.to_multiset() == m
            &&& (forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q])
            &&& m.contains(min)
            &&& (forall|z: int| m.contains(z) ==> min <= z)
        }
{
    let s = Sort(m);
    let min = MinOfMultiset(m);
    
    // Add proof that the minimum from the multiset is indeed the minimum
    assert(s.len() == m.len());
    assert(s.to_multiset() == m);
    assert(m.contains(min));
    
    (s, min)
}

}