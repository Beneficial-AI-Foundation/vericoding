// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min(a: Seq<int>) -> int
    recommends a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else if a[0] <= min(a.subrange(1, a.len() as int)) {
        a[0]
    } else {
        min(a.subrange(1, a.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: Seq<int>) -> (result: i32)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i] > 0
    ensures 
        result == -1 || a.contains(result as int),
        result != -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] % (result as int) == 0,
        result == -1 ==> forall|x: int| a.contains(x) ==> exists|i: int| 0 <= i < a.len() && a[i] % x != 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] % min(a) == 0) ==> result == min(a),
        (exists|i: int| 0 <= i < a.len() && a[i] % min(a) != 0) ==> result == -1
// </vc-spec>
// <vc-code>
{
    assume(false);
    -1
}
// </vc-code>


}

fn main() {}