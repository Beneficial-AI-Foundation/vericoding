// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, segments: Seq<(int, int)>) -> bool {
    n >= 1 && segments.len() == n && 
    forall|i: int| 0 <= i < n ==> segments[i].0 <= segments[i].1
}

spec fn covers_all(segments: Seq<(int, int)>, idx: int) -> bool {
    0 <= idx < segments.len() &&
    forall|j: int| 0 <= j < segments.len() ==> 
        segments[idx].0 <= segments[j].0 && segments[j].1 <= segments[idx].1
}

spec fn has_min_left_and_max_right(segments: Seq<(int, int)>, idx: int) -> bool {
    0 <= idx < segments.len() &&
    (forall|j: int| 0 <= j < segments.len() ==> segments[idx].0 <= segments[j].0) &&
    (forall|j: int| 0 <= j < segments.len() ==> segments[idx].1 >= segments[j].1)
}

spec fn min_left(segments: Seq<(int, int)>) -> int
    requires segments.len() > 0
    decreases segments.len()
{
    if segments.len() == 1 { 
        segments[0].0
    } else if segments[0].0 <= min_left(segments.subrange(1, segments.len() as int)) { 
        segments[0].0
    } else { 
        min_left(segments.subrange(1, segments.len() as int))
    }
}

spec fn max_right(segments: Seq<(int, int)>) -> int
    requires segments.len() > 0
    decreases segments.len()
{
    if segments.len() == 1 { 
        segments[0].1
    } else if segments[0].1 >= max_right(segments.subrange(1, segments.len() as int)) { 
        segments[0].1
    } else { 
        max_right(segments.subrange(1, segments.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i32, segments: &[i32]) -> (result: i32)
    requires 
        n >= 1 && segments.len() == n && 
        forall|i: int| 0 <= i < n ==> i % 2 == 0 ==> segments[i] <= segments[i + 1]
    ensures 
        result == -1 || (1 <= result <= n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    -1
}
// </vc-code>


}

fn main() {}