// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_upto(a: Seq<int>, end: int) -> int
    recommends -1 <= end < a.len()
    decreases end + 1
    when end >= -1
{
    if end == -1 {
        0
    } else {
        a[end] + sum_upto(a, end - 1)
    }
}

spec fn sum(a: Seq<int>) -> int {
    sum_upto(a, a.len() - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::external_body]
fn percentile_non_unique_answer() -> (result: (i8, Vec<i8>, i8, i8, i8))
    ensures 
        forall|i: int| 0 <= i < result.1@.len() ==> result.1@[i] as int > 0,
        0 <= result.0 as int && result.0 as int <= 100,
        result.2 as int == sum(result.1@.map(|i, x: i8| x as int)),
        result.2 as int > 0,
        -1 <= result.3 as int && (result.3 as int) < (result.1@.len() as int),
        sum_upto(result.1@.map(|i, x: i8| x as int), result.3 as int) <= (result.0 as int/100) * result.2 as int,
        (result.3 as int+1 < result.1@.len()) ==> sum_upto(result.1@.map(|i, x: i8| x as int), result.3 as int+1) >= (result.0 as int/100) * result.2 as int,
        -1 <= result.4 as int && (result.4 as int) < (result.1@.len() as int),
        sum_upto(result.1@.map(|i, x: i8| x as int), result.4 as int) <= (result.0 as int/100) * result.2 as int,
        (result.4 as int+1 < result.1@.len()) ==> sum_upto(result.1@.map(|i, x: i8| x as int), result.4 as int+1) >= (result.0 as int/100) * result.2 as int,
        result.3 != result.4
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}