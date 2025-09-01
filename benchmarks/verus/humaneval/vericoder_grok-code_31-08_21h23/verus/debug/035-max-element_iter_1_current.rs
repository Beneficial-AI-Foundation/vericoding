use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers required for this implementation
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut max = a[0];
    let mut index = 1;
    while index < a.len()
        invariant
            0 <= index <= a.len(),
            forall|[#trigger] a[old(j)].view().0(), old(j): int| old(j) >= 0 && old(j) < index ==> a[old(j)] <= max,
            exists|j: int| #![trigger a[j].view().0()] #![trigger] (j >= 0 && j < index && a[j] == max),
    {
        if a[index] > max {
            max = a[index];
        }
        index += 1;
    }
    assert(forall|i: int| 
        #![trigger a[i].view().0()], 
        i >= 0 && i < a.len() ==> a[i] <= max);
    assert(exists|i: int| 
        #![trigger a[i].view().0()], 
        i >= 0 && i < a.len() && a[i] == max);
    max
}
// </vc-code>

fn main() {}
}