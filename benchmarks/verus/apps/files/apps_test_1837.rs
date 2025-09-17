// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 &&
    a.len() == n &&
    (forall|i: int| 0 <= i < n ==> 0 <= a[i] < n) &&
    (forall|i: int, j: int| 0 <= i < j < n ==> a[i] != a[j]) &&
    (forall|k: int| #![trigger a[k]] 0 <= k < n ==> exists|i: int| 0 <= i < n && a[i] == k)
}

spec fn current_fixed_points(a: Seq<int>) -> int
    recommends a.len() >= 0
{
    Set::new(|i: int| 0 <= i < a.len() && a[i] == i).len() as int
}

spec fn max_possible_fixed_points(a: Seq<int>) -> int
    recommends valid_input(a.len() as int, a)
{
    let current = current_fixed_points(a);
    if current == a.len() as int {
        a.len() as int
    } else if exists|i: int| 0 <= i < a.len() && a[i] != i && a[a[i]] == i {
        current + 2
    } else {
        current + 1
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: Seq<int>) -> (result: int)
    requires 
        valid_input(n, a)
    ensures 
        result == max_possible_fixed_points(a),
        result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}