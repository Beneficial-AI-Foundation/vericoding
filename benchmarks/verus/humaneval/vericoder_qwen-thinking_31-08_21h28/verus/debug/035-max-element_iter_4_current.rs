use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n = a.len() as int;
    let mut max = a[0];
    let mut i: int = 1;
    while i < n {
        invariant (forall (j: int) :: 0 <= j && j < i ==> a@[j] <= max);
        invariant (exists (j: int) :: 0 <= j && j < i && a@[j] == max);
        if a[i as usize] > max {
            max = a[i as usize];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

fn main() {}
}