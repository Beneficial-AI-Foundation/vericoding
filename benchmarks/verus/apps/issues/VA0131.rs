// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_negative_temp_days(temps: Seq<int>) -> int
    decreases temps.len()
{
    if temps.len() == 0 {
        0int
    } else {
        (if temps[0] < 0 { 1int } else { 0int }) + count_negative_temp_days(temps.subrange(1, temps.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, temps: Vec<i8>) -> (result: i8)
    requires 
        n >= 1,
        k >= 0 && k <= n,
        temps@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==> #[trigger] temps@[i] as int >= -20 && #[trigger] temps@[i] as int <= 20,
    ensures 
        result as int == -1 <==> count_negative_temp_days(temps@.map(|i, x: i8| x as int)) > k as int,
        result != -1 ==> result >= 0,
        result as int == 0 ==> forall|i: int| 0 <= i < n as int ==> #[trigger] temps@[i] as int >= 0,
        result > 0 ==> exists|i: int| 0 <= i < n as int && #[trigger] temps@[i] as int < 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    0i8
}
// </vc-code>


}

fn main() {}