// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_beautiful_arrangement(arrangement: Seq<int>, sizes: Seq<int>) -> bool {
    arrangement.len() >= 1 &&
    (forall|i: int, j: int| #![trigger arrangement[i], arrangement[j]] 0 <= i < j < arrangement.len() ==> arrangement[i] != arrangement[j]) &&
    (forall|i: int| #![trigger arrangement[i]] 0 <= i < arrangement.len() - 1 ==> arrangement[i] < arrangement[i + 1]) &&
    (forall|i: int| #![trigger arrangement[i]] 0 <= i < arrangement.len() - 1 ==> arrangement[i + 1] % arrangement[i] == 0) &&
    (forall|i: int| #![trigger arrangement[i]] 0 <= i < arrangement.len() - 1 ==> 
        0 <= arrangement[i] - 1 < sizes.len() && 
        0 <= arrangement[i + 1] - 1 < sizes.len() &&
        sizes[arrangement[i] - 1] < sizes[arrangement[i + 1] - 1])
}

spec fn valid_input(n: int, sizes: Seq<int>) -> bool {
    n >= 1 && sizes.len() == n && forall|i: int| #![trigger sizes[i]] 0 <= i < n ==> sizes[i] >= 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, sizes: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, sizes@.map(|x: int, v: i8| v as int))
    ensures 1 <= result as int <= n as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}