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
/* helper modified by LLM (iteration 4): Added named return to ensure clause functions */
spec fn mapped_reps(reps: &Vec<i8>) -> Seq<int>
{
    reps@.map(|i: int, x: i8| x as int)
}

fn chest_total_exec(reps: &Vec<i8>) -> (result: i32)
    requires
        valid_input(mapped_reps(reps))
    ensures
        chest_total(mapped_reps(reps)) == result as int
{
    let mut sum = 0i32;
    let mut i = 0;
    let len = reps.len();
    while i < len
        invariant
            0 <= i <= len,
            sum as int == chest_total(mapped_reps(reps).subrange(0, i as int))
        decreases len - i
    {
        if i % 3 == 0 {
            sum += reps[i] as i32;
        }
        i += 1;
    }
    sum
}

fn biceps_total_exec(reps: &Vec<i8>) -> (result: i32)
    requires
        valid_input(mapped_reps(reps))
    ensures
        biceps_total(mapped_reps(reps)) == result as int
{
    let mut sum = 0i32;
    let mut i = 0;
    let len = reps.len();
    while i < len
        invariant
            0 <= i <= len,
            sum as int == biceps_total(mapped_reps(reps).subrange(0, i as int))
        decreases len - i
    {
        if i % 3 == 1 {
            sum += reps[i] as i32;
        }
        i += 1;
    }
    sum
}

fn back_total_exec(reps: &Vec<i8>) -> (result: i32)
    requires
        valid_input(mapped_reps(reps))
    ensures
back_total(mapped_reps(reps)) == result as int
{
    let mut sum = 0i32;
    let mut i = 0;
    let len = reps.len();
    while i < len
        invariant
            0 <= i <= len,
            sum as int == back_total(mapped_reps(reps).subrange(0, i as int))
        decreases len - i
    {
        if i % 3 == 2 {
            sum += reps[i] as i32;
        }
        i += 1;
    }
    sum
}

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
    /* code modified by LLM (iteration 4): no changes needed as error was in helpers */
    let chest = chest_total_exec(&reps);
    let biceps = biceps_total_exec(&reps);
    let back = back_total_exec(&reps);
    if chest >= biceps && chest >= back {
        "chest"
    } else if biceps > chest && biceps >= back {
        "biceps"
    } else {
        "back"
    }
}
// </vc-code>


}

fn main() {}