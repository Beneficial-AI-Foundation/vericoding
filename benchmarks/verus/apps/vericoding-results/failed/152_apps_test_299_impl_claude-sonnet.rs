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
/* helper modified by LLM (iteration 5): added trigger annotation to fix quantifier */
proof fn lemma_modulo_3_coverage()
    ensures
        forall|i: int| #[trigger] (i % 3) == 0 || i % 3 == 1 || i % 3 == 2
{
}

proof fn lemma_chest_total_equiv(reps: Seq<int>)
    requires reps.len() > 0
    ensures chest_total(reps) == chest_total_helper(reps, 0int)
    decreases reps.len()
{
    if reps.len() == 1 {
        assert(chest_total_helper(reps.subrange(1, reps.len() as int), 1int) == 0);
    } else {
        lemma_chest_total_equiv(reps.subrange(1, reps.len() as int));
    }
}

proof fn lemma_biceps_total_equiv(reps: Seq<int>)
    requires reps.len() > 0
    ensures biceps_total(reps) == biceps_total_helper(reps, 0int)
    decreases reps.len()
{
    if reps.len() == 1 {
        assert(biceps_total_helper(reps.subrange(1, reps.len() as int), 1int) == 0);
    } else {
        lemma_biceps_total_equiv(reps.subrange(1, reps.len() as int));
    }
}

proof fn lemma_back_total_equiv(reps: Seq<int>)
    requires reps.len() > 0
    ensures back_total(reps) == back_total_helper(reps, 0int)
    decreases reps.len()
{
    if reps.len() == 1 {
        assert(back_total_helper(reps.subrange(1, reps.len() as int), 1int) == 0);
    } else {
        lemma_back_total_equiv(reps.subrange(1, reps.len() as int));
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
{
    /* code modified by LLM (iteration 5): unchanged implementation */
    let ghost reps_seq = reps@.map(|i: int, x: i8| x as int);
    
    let mut chest_sum = 0i32;
    let mut biceps_sum = 0i32;
    let mut back_sum = 0i32;
    
    let mut index = 0usize;
    
    while index < reps.len()
        invariant
            index <= reps.len(),
            chest_sum >= 0,
            biceps_sum >= 0,
            back_sum >= 0,
            chest_sum == chest_total_helper(reps_seq.subrange(0, index as int), 0int),
            biceps_sum == biceps_total_helper(reps_seq.subrange(0, index as int), 0int),
            back_sum == back_total_helper(reps_seq.subrange(0, index as int), 0int)
        decreases reps.len() - index
    {
        let rep_value = reps[index] as i32;
        
        if index % 3 == 0 {
            chest_sum = chest_sum + rep_value;
        } else if index % 3 == 1 {
            biceps_sum = biceps_sum + rep_value;
        } else {
            back_sum = back_sum + rep_value;
        }
        
        index = index + 1;
    }
    
    proof {
        lemma_chest_total_equiv(reps_seq);
        lemma_biceps_total_equiv(reps_seq);
        lemma_back_total_equiv(reps_seq);
    }
    
    if chest_sum >= biceps_sum && chest_sum >= back_sum {
        "chest"
    } else if biceps_sum > chest_sum && biceps_sum >= back_sum {
        "biceps"
    } else {
        "back"
    }
}
// </vc-code>


}

fn main() {}