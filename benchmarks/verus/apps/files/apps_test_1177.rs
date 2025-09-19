// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, s as int, a@.map(|i: int, x: i8| x as int)),
    ensures 
        valid_result(result as int),
        (result as int) % 998244353 == (result as int),
        (n as int == 1 && s as int == a@.map(|i: int, x: i8| x as int)[0]) ==> (result as int) == single_element_case(n as int, s as int, a@.map(|i: int, x: i8| x as int)),
        (n as int == 1 && s as int != a@.map(|i: int, x: i8| x as int)[0]) ==> (result as int) == single_element_case(n as int, s as int, a@.map(|i: int, x: i8| x as int)),
        all_elements_greater_than_s(a@.map(|i: int, x: i8| x as int), s as int) ==> (result as int) == 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}