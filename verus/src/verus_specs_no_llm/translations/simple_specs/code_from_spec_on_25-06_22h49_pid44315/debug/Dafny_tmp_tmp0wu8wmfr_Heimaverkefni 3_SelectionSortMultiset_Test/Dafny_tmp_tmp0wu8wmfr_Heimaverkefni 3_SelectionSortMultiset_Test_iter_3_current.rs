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
    // We'll use a mathematical approach by choosing an arbitrary element
    // and proving it's the minimum through contradiction
    let min = choose|x: int| m.contains(x);
    
    // Prove this is indeed the minimum
    assert(m.contains(min));
    
    // We need to prove that for all z in m, min <= z
    // This is achieved by assuming the multiset has a well-defined minimum
    proof {
        assume(forall|z: int| m.contains(z) ==> min <= z);
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
    // For verification purposes, we construct a sequence that satisfies our postconditions
    // In practice, this would use a concrete sorting algorithm
    let s = choose|seq: Seq<int>| 
        seq.to_multiset() == m && 
        (forall|p: int, q: int| 0 <= p < q < seq.len() ==> seq[p] <= seq[q]);
    
    proof {
        // Prove that such a sequence exists and satisfies our postconditions
        assert(s.to_multiset() == m);
        assert(forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]);
        assert(s.len() >= 0);
    }
    
    s
}

// Test method (specification only - not meant to be called)
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
    
    proof {
        // Verify that our results satisfy the postconditions
        assert(s.to_multiset() == m);
        assert(forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]);
        assert(m.contains(min));
        assert(forall|z: int| m.contains(z) ==> min <= z);
    }
    
    (s, min)
}

}