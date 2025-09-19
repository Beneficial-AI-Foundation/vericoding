// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(l: Seq<nat>) -> nat
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else {
        l[0] + sum(l.skip(1))
    }
}

spec fn minimum(l: Seq<nat>) -> nat
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else if l.len() == 1 {
        l[0]
    } else {
        if l[0] <= minimum(l.skip(1)) { l[0] } else { minimum(l.skip(1)) }
    }
}

spec fn maximum(l: Seq<nat>) -> nat
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else if l.len() == 1 {
        l[0]
    } else {
        if l[0] >= maximum(l.skip(1)) { l[0] } else { maximum(l.skip(1)) }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn calculate_min_cost(n: nat, arr: Vec<nat>, m: nat, offers: Vec<Vec<nat>>) -> (result: nat)
    requires n == arr.len(),
    ensures 
        result <= sum(arr@),
        n == 1 ==> result == arr[0],
        (n == 2 && exists|o: Vec<nat>| #[trigger] offers@.contains(o) && o.len() >= 2) 
            ==> result <= sum(arr@) && (arr.len() > 0 ==> result >= maximum(arr@)),
        (n == 4 && offers.len() >= 4 && arr.len() > 0) ==> result <= sum(arr@) - minimum(arr@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {
    /* Apps difficulty: interview
    Assurance level: unguarded

    #eval calculate_min_cost 4 [1, 2, 3, 4] 3 [[2, 1, 2], [2, 3, 4], [3, 1, 2, 3]]
    Expected: 6

    #eval calculate_min_cost 3 [1, 2, 3] 1 [[2, 1, 2]]
    Expected: 4

    #eval calculate_min_cost 2 [5, 10] 1 [[2, 1, 2]]
    Expected: 10 */
}