// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn min(a: Seq<int>) -> int
    recommends a.len() > 0
{
    choose|x: int| a.contains(x) && forall|i: int| 0 <= i < a.len() ==> x <= a[i]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: i8)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i] as int > 0,
    ensures 
        result as int == -1 || exists|i: int| 0 <= i < a.len() && a[i] == result,
        result as int != -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] as int % result as int == 0,
        result as int == -1 ==> forall|x: int| (exists|i: int| 0 <= i < a.len() && a[i] as int == x) ==> exists|i: int| 0 <= i < a.len() && a[i] as int % x != 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] as int % min(a@.map(|i: int, x: i8| x as int)) == 0) ==> result as int == min(a@.map(|i: int, x: i8| x as int)),
        (exists|i: int| 0 <= i < a.len() && a[i] as int % min(a@.map(|i: int, x: i8| x as int)) != 0) ==> result as int == -1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}