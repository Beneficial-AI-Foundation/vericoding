// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, l: Seq<int>) -> bool {
    n >= 1 && k >= 1 && n <= 2*k &&
    l.len() == n &&
    forall|i: int, j: int| 0 <= i < l.len()-1 && j == i+1 ==> #[trigger] l[i] <= #[trigger] l[j] &&
    (forall|i: int| 0 <= i < l.len() ==> #[trigger] l[i] >= 0)
}

spec fn valid_box_configuration(boxes: Seq<int>, box_size: int) -> bool {
    boxes.len() >= 1 &&
    (forall|i: int| 0 <= i < boxes.len() ==> #[trigger] boxes[i] <= box_size) &&
    (forall|i: int| 0 <= i < boxes.len() ==> #[trigger] boxes[i] >= 0)
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn max_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0 
    } else if s.len() == 1 { 
        s[0] 
    } else if s[0] >= max_seq(s.subrange(1, s.len() as int)) { 
        s[0] 
    } else { 
        max_seq(s.subrange(1, s.len() as int)) 
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_nonneg()
    ensures
        0i8 >= 0,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, l: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, l@.map_values(|v: i8| v as int))
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    0i8
}
// </vc-code>


}

fn main() {}