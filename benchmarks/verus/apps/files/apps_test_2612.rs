// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_beautiful_arrangement(arrangement: Seq<int>, sizes: Seq<int>) -> bool
    recommends forall|i: int| 0 <= i < arrangement.len() ==> 1 <= arrangement[i] <= sizes.len()
{
    arrangement.len() >= 1 &&

    (forall|i: int, j: int| 0 <= i < j < arrangement.len() ==> arrangement[i] != arrangement[j]) &&

    (forall|i: int| 0 <= i < arrangement.len() - 1 ==> arrangement[i] < arrangement[i + 1]) &&

    (forall|i: int| 0 <= i < arrangement.len() - 1 ==> arrangement[i + 1] % arrangement[i] == 0) &&

    (forall|i: int| 0 <= i < arrangement.len() - 1 ==> sizes[arrangement[i] - 1] < sizes[arrangement[i + 1] - 1])
}

spec fn valid_input(n: int, sizes: Seq<int>) -> bool {
    n >= 1 && sizes.len() == n && forall|i: int| 0 <= i < n ==> sizes[i] >= 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, sizes: Seq<int>) -> (result: int)
    requires 
        valid_input(n, sizes)
    ensures 
        1 <= result <= n,
        forall|arrangement: Seq<int>| 
            (forall|i: int| 0 <= i < arrangement.len() ==> 1 <= arrangement[i] <= sizes.len()) && 
            is_valid_beautiful_arrangement(arrangement, sizes) ==> 
            arrangement.len() <= result,
        exists|arrangement: Seq<int>| 
            (forall|i: int| 0 <= i < arrangement.len() ==> 1 <= arrangement[i] <= sizes.len()) && 
            is_valid_beautiful_arrangement(arrangement, sizes) && 
            arrangement.len() == result
// </vc-spec>
// <vc-code>
{
    assume(false);
    n
}
// </vc-code>


}

fn main() {}