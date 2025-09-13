// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_negative_temp_days(temps: Seq<int>) -> int
    decreases temps.len()
{
    if temps.len() == 0 {
        0int
    } else {
        (if temps[0] < 0 { 1int } else { 0int }) + count_negative_temp_days(temps.subrange(1, temps.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, temps: Seq<int>) -> (result: int)
    requires 
        n >= 1,
        k >= 0 && k <= n,
        temps.len() == n,
        forall|i: int| 0 <= i < n ==> -20 <= temps[i] <= 20,
    ensures 
        result == -1 <==> count_negative_temp_days(temps) > k,
        result != -1 ==> result >= 0,
        result == 0 ==> forall|i: int| 0 <= i < n ==> temps[i] >= 0,
        result > 0 ==> exists|i: int| 0 <= i < n && temps[i] < 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}