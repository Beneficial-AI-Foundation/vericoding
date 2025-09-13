// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, s: int, a: Seq<int>) -> bool {
    n >= 1 && s >= 1 && a.len() == n && n <= 3000 && s <= 3000 &&
    forall|i: int| 0 <= i < n ==> a[i] >= 1 && a[i] <= 3000
}

spec fn valid_result(result: int) -> bool {
    result >= 0 && result < 998244353
}

spec fn all_elements_greater_than_s(a: Seq<int>, s: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] > s
}

spec fn single_element_case(n: int, s: int, a: Seq<int>) -> int
    decreases n
{
    if n == 1 && a.len() == 1 {
        if s == a[0] { 1 } else { 0 }
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, s: int, a: Seq<int>) -> (result: int)
    requires 
        valid_input(n, s, a),
    ensures 
        valid_result(result),
        result % 998244353 == result,
        (n == 1 && s == a[0]) ==> result == single_element_case(n, s, a),
        (n == 1 && s != a[0]) ==> result == single_element_case(n, s, a),
        all_elements_greater_than_s(a, s) ==> result == 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}