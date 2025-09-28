use vstd::prelude::*;

verus! {

// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>
// Helper predicate to define what it means to be the second largest element
spec fn is_second_largest(a: Seq<i32>, seclar: i32) -> bool {
    exists|largest_idx: int| 
        0 <= largest_idx < a.len() &&
        // There exists a largest element
        (forall|j: int| 0 <= j < a.len() ==> a[largest_idx] >= a[j]) &&
        // seclar is less than or equal to the largest
        seclar <= a[largest_idx] &&
        // seclar is greater than or equal to all elements except the largest
        (forall|j: int| 0 <= j < a.len() && a[j] != a[largest_idx] ==> seclar >= a[j]) &&
        // seclar appears in the array or equals the largest (handles case where all elements are equal)
        (exists|k: int| 0 <= k < a.len() && a[k] == seclar)
}

// Helper lemma to prove properties about max finding
proof fn lemma_max_properties(a: Seq<i32>, max_idx: int)
    requires 
        a.len() > 0,
        0 <= max_idx < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[max_idx] >= a[j]
    ensures
        forall|j: int| 0 <= j < a.len() ==> a[j] <= a[max_idx]
{
}
// </vc-helpers>

// <vc-spec>
fn second_largest(a: &[i32]) -> (seclar: i32)
    requires a.len() > 0
    //ensures exists i :: 0 <= i < a.len() && forall j :: (0 <= j < a.len() && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
// </vc-spec>
// <vc-code>
{
    let mut largest = a[0];
    let mut second = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant 
            1 <= i <= a.len(),
            // largest is the maximum of elements seen so far
            forall|j: int| 0 <= j < i ==> a@[j] <= largest,
            exists|k: int| 0 <= k < i && a@[k] == largest,
            // second is the second largest (or equal to largest if all elements seen are equal)
            forall|j: int| 0 <= j < i ==> (a@[j] == largest || a@[j] <= second),
            exists|k: int| 0 <= k < i && a@[k] == second,
            second <= largest
        decreases a.len() - i
    {
        if a[i] > largest {
            second = largest;
            largest = a[i];
        } else if a[i] > second {
            second = a[i];
        }
        i += 1;
    }
    
    proof {
        // After the loop, we have the invariants for the entire array
        assert(forall|j: int| 0 <= j < a.len() ==> a@[j] <= largest);
        assert(exists|k: int| 0 <= k < a.len() && a@[k] == largest);
        assert(forall|j: int| 0 <= j < a.len() ==> (a@[j] == largest || a@[j] <= second));
        assert(exists|k: int| 0 <= k < a.len() && a@[k] == second);
        
        // This means second is indeed the second largest value
        let largest_idx = choose|k: int| 0 <= k < a.len() && a@[k] == largest;
        assert(0 <= largest_idx < a.len());
        assert(forall|j: int| 0 <= j < a.len() ==> a@[largest_idx] >= a@[j]);
        assert(second <= a@[largest_idx]);
        assert(forall|j: int| 0 <= j < a.len() && a@[j] != a@[largest_idx] ==> second >= a@[j]);
        assert(exists|k: int| 0 <= k < a.len() && a@[k] == second);
        
        assert(is_second_largest(a@, second));
    }
    
    second
}
// </vc-code>

fn main() {
}

}