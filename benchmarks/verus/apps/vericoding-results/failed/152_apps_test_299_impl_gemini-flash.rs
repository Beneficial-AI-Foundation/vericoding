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
/* helper modified by LLM (iteration 5): Corrected forall parameters to be `index: int`, which will apply to `i: int` within the lambda. */
proof fn lemma_sum_parts_equals_total(reps: Seq<int>)
    requires
        reps.len() > 0
    ensures
        chest_total(reps) + biceps_total(reps) + back_total(reps) == reps.fold_left(|acc, x| acc + x, 0)
    decreases reps.len()
{
    if reps.len() == 1 {
        let r0 = reps[0];
        if 0int % 3 == 0 {
            assert(chest_total(reps) == r0);
            assert(biceps_total(reps) == 0);
            assert(back_total(reps) == 0);
        } else if 0int % 3 == 1 {
            assert(chest_total(reps) == 0);
            assert(biceps_total(reps) == r0);
            assert(back_total(reps) == 0);
        } else {
            assert(chest_total(reps) == 0);
            assert(biceps_total(reps) == 0);
            assert(back_total(reps) == r0);
        }
    } else {
        let chest_first = if 0int % 3 == 0 { reps[0int] } else { 0int };
        let biceps_first = if 0int % 3 == 1 { reps[0int] } else { 0int };
        let back_first = if 0int % 3 == 2 { reps[0int] } else { 0int };
        let remaining_reps = reps.subrange(1, reps.len() as int);

        lemma_sum_parts_equals_total_helper(remaining_reps, 1);

        assert(chest_total(reps) == chest_first + chest_total_helper(remaining_reps, 1));
        assert(biceps_total(reps) == biceps_first + biceps_total_helper(remaining_reps, 1));
        assert(back_total(reps) == back_first + back_total_helper(remaining_reps, 1));
        
        assert(chest_first + biceps_first + back_first == reps[0]);
        assert(chest_total_helper(remaining_reps, 1) + biceps_total_helper(remaining_reps, 1) + back_total_helper(remaining_reps, 1) == remaining_reps.fold_left(|acc, x: int| acc + x, 0));

        assert( (chest_first + chest_total_helper(remaining_reps, 1))
                + (biceps_first + biceps_total_helper(remaining_reps, 1))
                + (back_first + back_total_helper(remaining_reps, 1)) == reps[0] + remaining_reps.fold_left(|acc, x: int| acc + x, 0));
        assert(reps[0] + remaining_reps.fold_left(|acc, x: int| acc + x, 0) == reps.fold_left(|acc, x: int| acc + x, 0));
    }
}

proof fn lemma_sum_parts_equals_total_helper(reps: Seq<int>, index: int)
    requires
        index >= 0
    ensures
        chest_total_helper(reps, index) + biceps_total_helper(reps, index) + back_total_helper(reps, index)
            == reps.fold_left(|acc, x| acc + x, 0)
    decreases reps.len()
{
    if reps.len() == 1 {
        let r0 = reps[0];
        if index % 3 == 0 {
            assert(chest_total_helper(reps, index) == r0);
            assert(biceps_total_helper(reps, index) == 0);
            assert(back_total_helper(reps, index) == 0);
        } else if index % 3 == 1 {
            assert(chest_total_helper(reps, index) == 0);
            assert(biceps_total_helper(reps, index) == r0);
            assert(back_total_helper(reps, index) == 0);
        } else {
            assert(chest_total_helper(reps, index) == 0);
            assert(biceps_total_helper(reps, index) == 0);
            assert(back_total_helper(reps, index) == r0);
        }
    } else if reps.len() > 1 {
        let chest_first = if index % 3 == 0 { reps[0int] } else { 0int };
        let biceps_first = if index % 3 == 1 { reps[0int] } else { 0int };
        let back_first = if index % 3 == 2 { reps[0int] } else { 0int };
        let remaining_reps = reps.subrange(1, reps.len() as int);

        lemma_sum_parts_equals_total_helper(remaining_reps, index + 1);

        assert(chest_total_helper(reps, index) == chest_first + chest_total_helper(remaining_reps, index + 1));
        assert(biceps_total_helper(reps, index) == biceps_first + biceps_total_helper(remaining_reps, index + 1));
        assert(back_total_helper(reps, index) == back_first + back_total_helper(remaining_reps, index + 1));
        
        assert(chest_first + biceps_first + back_first == reps[0]);
        assert(chest_total_helper(remaining_reps, index + 1) + biceps_total_helper(remaining_reps, index + 1) + back_total_helper(remaining_reps, index + 1) == remaining_reps.fold_left(|acc, x: int| acc + x, 0));

        assert( (chest_first + chest_total_helper(remaining_reps, index + 1))
                + (biceps_first + biceps_total_helper(remaining_reps, index + 1))
                + (back_first + back_total_helper(remaining_reps, index + 1)) == reps[0] + remaining_reps.fold_left(|acc, x: int| acc + x, 0));
        assert(reps[0] + remaining_reps.fold_left(|acc, x: int| acc + x, 0) == reps.fold_left(|acc, x: int| acc + x, 0));
    }
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
/* code modified by LLM (iteration 5): Changed the type of the index `i` in map lambda from `nat` to `int` based on the error. */
{
    let reps_seq = reps@.map(|i: int, x: i8| x as int);

    let chest_total_val = chest_total(reps_seq);
    let biceps_total_val = biceps_total(reps_seq);
    let back_total_val = back_total(reps_seq);

    if chest_total_val >= biceps_total_val && chest_total_val >= back_total_val {
        "chest"
    } else if biceps_total_val > chest_total_val && biceps_total_val >= back_total_val {
        "biceps"
    } else {
        "back"
    }
}
// </vc-code>


}

fn main() {}