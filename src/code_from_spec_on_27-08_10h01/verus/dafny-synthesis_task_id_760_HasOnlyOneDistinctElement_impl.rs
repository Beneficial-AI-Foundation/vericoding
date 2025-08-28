use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn all_elements_equal(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]
}

spec fn exists_different_elements(a: &[i32]) -> bool {
    exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j]
}

proof fn lemma_empty_array_all_equal(a: &[i32])
    requires a.len() == 0
    ensures all_elements_equal(a)
{
}

proof fn lemma_single_element_all_equal(a: &[i32])
    requires a.len() == 1
    ensures all_elements_equal(a)
{
}

proof fn lemma_not_all_equal_implies_exists_different(a: &[i32])
    requires !all_elements_equal(a)
    ensures exists_different_elements(a)
{
}

proof fn lemma_all_equal_implies_not_exists_different(a: &[i32])
    requires all_elements_equal(a)
    ensures !exists_different_elements(a)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.len() <= 1 {
        proof {
            if a.len() == 0 {
                lemma_empty_array_all_equal(a);
            } else {
                lemma_single_element_all_equal(a);
            }
        }
        return true;
    }
    
    let first = a[0];
    for i in 1..a.len()
        invariant forall|k: int| 0 <= k < i ==> a[k] == first
    {
        if a[i] != first {
            proof {
                assert(a[0] != a[i as int]);
                assert(exists|x: int, y: int| 0 <= x < a.len() && 0 <= y < a.len() && a[x] != a[y]);
            }
            return false;
        }
    }
    
    proof {
        assert(forall|k: int| 0 <= k < a.len() ==> a[k] == first);
        assert(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]);
    }
    
    true
}
// </vc-code>

fn main() {}

}