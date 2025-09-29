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
/* helper modified by LLM (iteration 5): unchanged as fix was in vc-code */
fn compute_moves(a: i8, b: i8) -> (result: i8)
    requires
        a >= 1,
        b >= 1,
    ensures
        result as int == min_moves(a as int, b as int),
{
    if a == b {
        0
    } else if a < b {
        if (b - a) % 2 == 1 {
            1
        } else {
            2
        }
    } else { // a > b
        if (a - b) % 2 == 0 {
            1
        } else {
            2
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<(i8, i8)>) -> (result: Vec<i8>)
    requires valid_input(input@.map(|i, x: (i8, i8)| (x.0 as int, x.1 as int)))
    ensures valid_output(input@.map(|i, x: (i8, i8)| (x.0 as int, x.1 as int)), result@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by moving ghost code into a proof block */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            valid_input(input@.map(|i, x: (i8, i8)| (x.0 as int, x.1 as int))),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result@[j] as int == min_moves(input@[j].0 as int, input@[j].1 as int),
        decreases input.len() - i
    {
        let item = input[i];
        let a = item.0;
        let b = item.1;

        assert(a >= 1 && b >= 1) by {
            let mapped_input = input@.map(|i, x: (i8, i8)| (x.0 as int, x.1 as int));
            assert(valid_input(mapped_input));
            assert(mapped_input[i as int].0 >= 1 && mapped_input[i as int].1 >= 1);
            assert(a as int == mapped_input[i as int].0);
            assert(b as int == mapped_input[i as int].1);
        };

        let moves = compute_moves(a, b);
        result.push(moves);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}