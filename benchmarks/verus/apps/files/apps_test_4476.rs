// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < input.len() ==> input[i].0 >= 1 && input[i].1 >= 1
}

spec fn min_moves(a: int, b: int) -> int
    recommends a >= 1 && b >= 1
{
    if a == b {
        0
    } else if a < b {
        if (b - a) % 2 == 1 { 1 } else { 2 }
    } else {
        if (a - b) % 2 == 0 { 1 } else { 2 }
    }
}

spec fn valid_output(input: Seq<(int, int)>, result: Seq<int>) -> bool {
    valid_input(input) ==> (
        result.len() == input.len() &&
        forall|i: int| 0 <= i < input.len() ==> result[i] == min_moves(input[i].0, input[i].1) &&
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0
    )
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<(i8, i8)>) -> (result: Vec<i8>)
    requires valid_input(input@.map(|i, x: (i8, i8)| (x.0 as int, x.1 as int)))
    ensures valid_output(input@.map(|i, x: (i8, i8)| (x.0 as int, x.1 as int)), result@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}