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
/* helper modified by LLM (iteration 5): No changes were needed, just updating the iteration comment. The helper is not strictly required but preserved. */
proof fn sum_of_two(a: int, b: int)
    ensures
        sum(seq![a, b]) == a + b,
{
    let s = seq![a, b];
    assert(sum(s) == sum_upto(s, 1));
    assert(sum_upto(s, 1) == s[1] + sum_upto(s, 0));
    assert(sum_upto(s, 0) == s[0] + sum_upto(s, -1));
    assert(sum_upto(s, -1) == 0);
    assert(s[0] == a);
    assert(s[1] == b);
}
// </vc-helpers>

// <vc-spec>
#[verifier::external_body]
fn percentile_non_unique_answer() -> (result: (int, Vec<int>, int, int, int))
    ensures 
        forall|i: int| 0 <= i < result.1@.len() ==> result.1@[i] > 0,
        0 <= result.0 && result.0 <= 100,
        result.2 == sum(result.1@),
        result.2 > 0,
        -1 <= result.3 && result.3 < result.1@.len(),
        sum_upto(result.1@, result.3) <= (result.0/100) * result.2,
        result.3+1 < result.1@.len() ==> sum_upto(result.1@, result.3+1) >= (result.0/100) * result.2,
        -1 <= result.4 && result.4 < result.1@.len(),
        sum_upto(result.1@, result.4) <= (result.0/100) * result.2,
        result.4+1 < result.1@.len() ==> sum_upto(result.1@, result.4+1) >= (result.0/100) * result.2,
        result.3 != result.4
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add explicit 'as int' casts to fix compilation type errors */
    (100 as int, vec![10 as int, 10 as int], 20 as int, 1 as int, 0 as int)
}
// </vc-code>

}
fn main() {}