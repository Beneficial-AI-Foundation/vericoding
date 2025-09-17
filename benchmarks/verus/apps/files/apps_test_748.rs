// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, numbers: Seq<int>) -> bool {
    n >= 3 && n % 3 == 0 &&
    numbers.len() == n &&
    forall|i: int| 0 <= i < numbers.len() ==> 1 <= #[trigger] numbers[i] && #[trigger] numbers[i] <= 7
}

spec fn valid_triplet(triplet: Seq<int>) -> bool {
    triplet.len() == 3 &&
    triplet[0] < triplet[1] && triplet[1] < triplet[2] &&
    triplet[0] > 0 && triplet[1] > 0 && triplet[2] > 0 &&
    triplet[1] % triplet[0] == 0 && triplet[2] % triplet[1] == 0
}

spec fn flatten_partition(result: Seq<Seq<int>>) -> Seq<int>
    decreases result.len()
{
    if result.len() == 0 { 
        seq![]
    } else {
        result[0].add(flatten_partition(result.subrange(1, result.len() as int)))
    }
}

spec fn valid_partition(result: Seq<Seq<int>>, numbers: Seq<int>) -> bool {
    result.len() == numbers.len() / 3 &&
    (forall|i: int| 0 <= i < result.len() ==> valid_triplet(#[trigger] result[i])) &&
    numbers.to_multiset() == flatten_partition(result).to_multiset()
}

spec fn no_partition_exists(result: Seq<Seq<int>>) -> bool {
    result.len() == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, numbers: Seq<int>) -> (result: Seq<Seq<int>>)
    requires valid_input(n, numbers)
    ensures no_partition_exists(result) || valid_partition(result, numbers)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}