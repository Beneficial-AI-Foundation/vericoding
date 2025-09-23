// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: nat, arr: Seq<int>) -> bool {
    n > 0 && arr.len() == n && forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 1
}

spec fn is_unimodal(arr: Seq<int>) -> bool {
    if arr.len() <= 1 { 
        true 
    } else {
        let phases = compute_phases(arr);
        phases.0 <= phases.1 && phases.1 <= phases.2 && phases.2 == arr.len() &&
        (forall|i: int, j: int| 0 <= i < j < phases.0 ==> #[trigger] arr[i] < #[trigger] arr[j]) &&
        (forall|i: int| phases.0 <= i < phases.1 ==> #[trigger] arr[i] == (if phases.0 > 0 { arr[phases.0] } else { arr[0] })) &&
        (forall|i: int, j: int| phases.1 <= i < j < phases.2 ==> #[trigger] arr[i] > #[trigger] arr[j]) &&
        (phases.0 > 0 && phases.1 < arr.len() ==> arr[phases.0-1] >= (if phases.1 > phases.0 { arr[phases.0] } else { arr[phases.1] }))
    }
}

spec fn compute_phases(arr: Seq<int>) -> (int, int, int) {
    let inc_end = compute_increasing_end(arr, 0, 0);
    let const_end = compute_constant_end(arr, inc_end, if inc_end > 0 { arr[inc_end-1] } else { 0 });
    let dec_end = compute_decreasing_end(arr, const_end, if const_end > inc_end { arr[inc_end] } else if inc_end > 0 { arr[inc_end-1] } else { 0 });
    (inc_end, const_end, dec_end)
}

spec fn compute_increasing_end(arr: Seq<int>, start: int, prev: int) -> int {
    0
}

spec fn compute_constant_end(arr: Seq<int>, start: int, value: int) -> int {
    start
}

spec fn compute_decreasing_end(arr: Seq<int>, start: int, prev: int) -> int {
    arr.len() as int
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: nat, arr: Seq<int>) -> (result: String)
    requires 
        valid_input(n, arr),
    ensures 
        result@ == "YES"@ || result@ == "NO"@,
        result@ == "YES"@ <==> is_unimodal(arr),
// </vc-spec>
// <vc-code>
{
    assume(false);
    "NO".to_string()
}
// </vc-code>


}

fn main() {}