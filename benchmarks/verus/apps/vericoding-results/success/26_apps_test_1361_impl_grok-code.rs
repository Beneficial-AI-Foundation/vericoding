// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(holds: Seq<int>) -> bool {
    holds.len() >= 3 && forall|i: int| 0 <= i < holds.len() - 1 ==> #[trigger] holds[i] < holds[i + 1]
}

spec fn max_diff(s: Seq<int>) -> int {
    if s.len() <= 1 { 0 }
    else {
        let max_so_far = if s[1] - s[0] >= 0 { s[1] - s[0] } else { 0 };
        max_diff_helper(s, 2, max_so_far)
    }
}

spec fn max_diff_helper(s: Seq<int>, index: int, current_max: int) -> int
    decreases s.len() - index
{
    if index >= s.len() { current_max }
    else {
        let diff = s[index] - s[index - 1];
        let new_max = if diff > current_max { diff } else { current_max };
        max_diff_helper(s, index + 1, new_max)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(holds: Vec<i8>) -> (result: i8)
    requires valid_input(holds@.map(|i, x: i8| x as int))
    ensures result as int >= 0
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): clamped max_d to 127 to ensure result >=0 after cast */
    let mut max_d: i16 = 0;
    let mut i: usize = 1;
    while i < holds.len()
        invariant
            1 <= (i as int) <= holds@.len(),
            max_d >= 0,
            0 <= holds@.len()
        decreases holds@.len() - (i as int)
    {
        let prev = holds[i - 1] as i16;
        let curr = holds[i] as i16;
        let diff = curr - prev;
        if diff > max_d {
            max_d = diff;
        }
        i = i + 1;
    }
    let result_max = if max_d > 127 { 127 } else { max_d };
    result_max as i8
}
// </vc-code>


}

fn main() {}