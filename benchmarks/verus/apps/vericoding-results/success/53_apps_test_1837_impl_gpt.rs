// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 &&
    a.len() == n &&
    (forall|i: int| #![trigger a[i]] 0 <= i < n ==> 0 <= a[i] < n) &&
    (forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i < j < n ==> a[i] != a[j]) &&
    (forall|k: int| #![trigger a[k]] 0 <= k < n ==> exists|i: int| 0 <= i < n && a[i] == k)
}

spec fn current_fixed_points(a: Seq<int>) -> int {
    a.len() as int
}

spec fn max_possible_fixed_points(a: Seq<int>) -> int 
    recommends valid_input(a.len() as int, a)
{
    let current = current_fixed_points(a);
    if current == a.len() {
        a.len() as int
    } else if exists|i: int| 0 <= i < a.len() && a[i] != i && a[a[i] as int] == i {
        current + 2
    } else {
        current + 1
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map(|i, x| x as int)),
    ensures 
        result as int == max_possible_fixed_points(a@.map(|i, x| x as int)),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    n
}
// </vc-code>


}

fn main() {}