// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 &&
    a.len() == n &&
    (forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= n) &&
    (forall|i: int, j: int| 0 <= i < j < n ==> a[i] != a[j])
}

spec fn valid_output(n: int, result: int) -> bool {
    0 <= result <= n
}

spec fn reversed_array(a: Seq<int>) -> Seq<int>
    recommends a.len() >= 1
{
    Seq::new(a.len(), |i: int| a[a.len() - 1 - i])
}

spec fn has_increasing_pair(ar: Seq<int>) -> bool {
    exists|i: int| 1 <= i < ar.len() && #[trigger] ar[i] > ar[i-1]
}

spec fn min_index(ar: Seq<int>, n: int) -> int {
    0
}

spec fn correct_result(n: int, a: Seq<int>) -> int
    recommends valid_input(n, a)
{
    let ar = reversed_array(a);
    if has_increasing_pair(ar) {
        let min_i = min_index(ar, n);
        n - min_i
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures 
        valid_output(n as int, result as int) &&
        result as int == correct_result(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}