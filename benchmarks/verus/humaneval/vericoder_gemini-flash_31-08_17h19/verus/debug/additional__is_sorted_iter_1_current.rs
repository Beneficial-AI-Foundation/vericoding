use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_non_decreasing(lst: &[i32]) -> (result: bool)
    ensures result <==> (forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j])
{
    let mut i: int = 0;
    let mut decreasing_found: bool = false;

    while (i + 1 < lst.len() as int)
        invariant
            0 <= i,
            i < lst.len() as int,
            decreasing_found == exists|k: int, l: int| 0 <= k && k < l && l < i + 1 && lst[k] > lst[l],
            !decreasing_found ==> forall|k: int, l: int| 0 <= k && k < l && l < i + 1 ==> lst[k] <= lst[l],
    {
        if lst[i as usize] > lst[(i + 1) as usize] {
            decreasing_found = true;
        }
        i = i + 1;
    }

    if decreasing_found {
        false
    } else {
        true
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    // pre-conditions-start
    requires
        lst.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut i: int = 0;
    let mut sorted_so_far: bool = true;

    while (i + 1 < lst.len() as int)
        invariant
            0 <= i,
            i < lst.len() as int,
            sorted_so_far ==> (forall|k: int, l: int| 0 <= k && k < l && l < i + 1 ==> lst[k] <= lst[l]),
            !sorted_so_far ==> (exists|k: int, l: int| 0 <= k && k < l && l < i + 1 && lst[k] > lst[l]),
    {
        if lst[i as usize] > lst[(i + 1) as usize] {
            sorted_so_far = false;
        }
        i = i + 1;
    }
    sorted_so_far
    // impl-end
}
// </vc-code>

fn main() {}
}