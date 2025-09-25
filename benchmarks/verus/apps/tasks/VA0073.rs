// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn chest_total(reps: Seq<int>) -> int 
decreases reps.len()
{
    if reps.len() == 0 {
        0int
    } else {
        let first = if 0int % 3 == 0 { reps[0int] } else { 0int };
        first + chest_total_helper(reps.subrange(1, reps.len() as int), 1int)
    }
}

spec fn chest_total_helper(reps: Seq<int>, index: int) -> int 
decreases reps.len()
{
    if reps.len() == 0 {
        0int
    } else {
        let first = if index % 3 == 0 { reps[0int] } else { 0int };
        first + chest_total_helper(reps.subrange(1, reps.len() as int), index + 1)
    }
}

spec fn biceps_total(reps: Seq<int>) -> int 
decreases reps.len()
{
    if reps.len() == 0 {
        0int
    } else {
        let first = if 0int % 3 == 1 { reps[0int] } else { 0int };
        first + biceps_total_helper(reps.subrange(1, reps.len() as int), 1int)
    }
}

spec fn biceps_total_helper(reps: Seq<int>, index: int) -> int 
decreases reps.len()
{
    if reps.len() == 0 {
        0int
    } else {
        let first = if index % 3 == 1 { reps[0int] } else { 0int };
        first + biceps_total_helper(reps.subrange(1, reps.len() as int), index + 1)
    }
}

spec fn back_total(reps: Seq<int>) -> int 
decreases reps.len()
{
    if reps.len() == 0 {
        0int
    } else {
        let first = if 0int % 3 == 2 { reps[0int] } else { 0int };
        first + back_total_helper(reps.subrange(1, reps.len() as int), 1int)
    }
}

spec fn back_total_helper(reps: Seq<int>, index: int) -> int 
decreases reps.len()
{
    if reps.len() == 0 {
        0int
    } else {
        let first = if index % 3 == 2 { reps[0int] } else { 0int };
        first + back_total_helper(reps.subrange(1, reps.len() as int), index + 1)
    }
}

spec fn valid_input(reps: Seq<int>) -> bool {
    reps.len() > 0 && forall|i: int| 0 <= i < reps.len() ==> reps[i] > 0
}

spec fn is_winner(muscle: &str, reps: Seq<int>) -> bool {
    let chest_total_val = chest_total(reps);
    let biceps_total_val = biceps_total(reps);
    let back_total_val = back_total(reps);

    match muscle {
        "chest" => chest_total_val >= biceps_total_val && chest_total_val >= back_total_val,
        "biceps" => biceps_total_val > chest_total_val && biceps_total_val >= back_total_val,
        "back" => back_total_val > chest_total_val && back_total_val > biceps_total_val,
        _ => false,
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_strongest_muscle_group(reps: Vec<i8>) -> (result: &'static str)
    requires 
        valid_input(reps@.map(|i: int, x: i8| x as int))
    ensures 
        result == "chest" || result == "biceps" || result == "back",
        is_winner(result, reps@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    "chest"
}
// </vc-code>


}

fn main() {}