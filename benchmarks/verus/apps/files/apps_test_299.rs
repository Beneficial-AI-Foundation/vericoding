// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn chest_total(reps: Seq<int>) -> int
    decreases reps.len()
{
    chest_total_helper(reps, 0int)
}

spec fn chest_total_helper(reps: Seq<int>, offset: int) -> int
    decreases reps.len()
{
    if reps.len() == 0 {
        0int
    } else {
        let first = if offset % 3int == 0int { reps[0] } else { 0int };
        first + chest_total_helper(reps.subrange(1, reps.len() as int), offset + 1int)
    }
}

spec fn biceps_total(reps: Seq<int>) -> int
    decreases reps.len()
{
    biceps_total_helper(reps, 0int)
}

spec fn biceps_total_helper(reps: Seq<int>, offset: int) -> int
    decreases reps.len()
{
    if reps.len() == 0 {
        0int
    } else {
        let first = if offset % 3int == 1int { reps[0] } else { 0int };
        first + biceps_total_helper(reps.subrange(1, reps.len() as int), offset + 1int)
    }
}

spec fn back_total(reps: Seq<int>) -> int
    decreases reps.len()
{
    back_total_helper(reps, 0int)
}

spec fn back_total_helper(reps: Seq<int>, offset: int) -> int
    decreases reps.len()
{
    if reps.len() == 0 {
        0int
    } else {
        let first = if offset % 3int == 2int { reps[0] } else { 0int };
        first + back_total_helper(reps.subrange(1, reps.len() as int), offset + 1int)
    }
}

spec fn valid_input(reps: Seq<int>) -> bool {
    reps.len() > 0 && forall|i: int| 0 <= i < reps.len() ==> reps[i] > 0
}

spec fn is_winner(muscle: String, reps: Seq<int>) -> bool
    recommends valid_input(reps)
{
    let chest_total_val = chest_total(reps);
    let biceps_total_val = biceps_total(reps);
    let back_total_val = back_total(reps);

    if muscle == "chest" {
        chest_total_val >= biceps_total_val && chest_total_val >= back_total_val
    } else if muscle == "biceps" {
        biceps_total_val > chest_total_val && biceps_total_val >= back_total_val
    } else if muscle == "back" {
        back_total_val > chest_total_val && back_total_val > biceps_total_val
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn find_strongest_muscle_group(reps: Seq<int>) -> (result: String)
    requires 
        valid_input(reps)
    ensures 
        result == "chest" || result == "biceps" || result == "back",
        is_winner(result, reps)
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}