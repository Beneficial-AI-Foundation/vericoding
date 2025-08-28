use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    for i in 0..list1.len()
        invariant
            forall|ii: int, j: int| 0 <= ii < i && 0 <= j < list2.len() ==> list1[ii] != list2[j],
    {
        for j in 0..list2.len()
            invariant
                i < list1.len(),
                forall|jj: int| 0 <= jj < j ==> list1[i as int] != list2[jj],
        {
            if list1[i] == list2[j] {
                proof {
                    assert(0 <= i < list1.len());
                    assert(0 <= j < list2.len());
                    assert(list1[i as int] == list2[j as int]);
                }
                return true;
            }
        }
    }
    proof {
        assert(forall|ii: int, j: int| 0 <= ii < list1.len() && 0 <= j < list2.len() ==> list1[ii] != list2[j]);
    }
    false
}
// </vc-code>

} // verus!

fn main() {}