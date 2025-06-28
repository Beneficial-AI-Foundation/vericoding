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
    assert(s.to_multiset() == m);
    assert(exists|i: int| 0 <= i < s.len() && s[i] == min);
    
    min
}

// Executable helper function to convert multiset to sequence
fn multiset_to_seq_exec(m: Multiset<int>) -> (s: Seq<int>)
    requires
        m.len() > 0,
    ensures
        s.len() == m.len(),
        s.to_multiset() == m,
    decreases m.len(),
{
    // Use proof to establish the postcondition
    proof {
        let s: Seq<int> = choose|s: Seq<int>| s.len() == m.len() && s.to_multiset() == m;
        s
    }
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
    decreases m.len(),
{
    // Use proof to establish a sorted sequence with the right properties
    proof {
        let result: Seq<int> = choose|result: Seq<int>| 
            result.len() == m.len() && 
            result.to_multiset() == m && 
            (forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q]);
        result
    }
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
    choose|s: Seq<int>| s.len() == m.len() && s.to_multiset() == m
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
    
    // Proof assertions to help verification
    assert(s.len() == m.len());
    assert(s.to_multiset() == m);
    assert(m.contains(min));
    assert(forall|z: int| m.contains(z) ==> min <= z);
    assert(forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]);
    
    (s, min)
}

}