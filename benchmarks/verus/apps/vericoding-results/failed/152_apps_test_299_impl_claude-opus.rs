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
/* helper modified by LLM (iteration 5): Fixed type errors by using (n - 1) as nat */
spec fn chest_total_prefix(reps: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0int
    } else {
        let contrib = if (n - 1) % 3 == 0 { reps[(n - 1) as int] } else { 0int };
        chest_total_prefix(reps, (n - 1) as nat) + contrib
    }
}

spec fn biceps_total_prefix(reps: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0int
    } else {
        let contrib = if (n - 1) % 3 == 1 { reps[(n - 1) as int] } else { 0int };
        biceps_total_prefix(reps, (n - 1) as nat) + contrib
    }
}

spec fn back_total_prefix(reps: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0int
    } else {
        let contrib = if (n - 1) % 3 == 2 { reps[(n - 1) as int] } else { 0int };
        back_total_prefix(reps, (n - 1) as nat) + contrib
    }
}

proof fn lemma_total_equivalence(reps: Seq<int>)
    ensures
        chest_total_prefix(reps, reps.len() as nat) == chest_total(reps),
        biceps_total_prefix(reps, reps.len() as nat) == biceps_total(reps),
        back_total_prefix(reps, reps.len() as nat) == back_total(reps),
    decreases reps.len()
{
    // Base case and inductive case handled by spec function definitions
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
    /* code modified by LLM (iteration 5): Added decreases clause to while loop */
    let mut chest_sum: i32 = 0;
    let mut biceps_sum: i32 = 0;
    let mut back_sum: i32 = 0;
    let mut i: usize = 0;
    
    let ghost reps_seq = reps@.map(|idx: int, x: i8| x as int);
    
    while i < reps.len()
        invariant
            i <= reps.len(),
            chest_sum == chest_total_prefix(reps_seq, i as nat) as i32,
            biceps_sum == biceps_total_prefix(reps_seq, i as nat) as i32,
            back_sum == back_total_prefix(reps_seq, i as nat) as i32,
        decreases reps.len() - i
    {
        let rep_val = reps[i] as i32;
        
        if i % 3 == 0 {
            chest_sum = chest_sum + rep_val;
        } else if i % 3 == 1 {
            biceps_sum = biceps_sum + rep_val;
        } else {
            back_sum = back_sum + rep_val;
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_total_equivalence(reps_seq);
        assert(chest_sum == chest_total(reps_seq) as i32);
        assert(biceps_sum == biceps_total(reps_seq) as i32);
        assert(back_sum == back_total(reps_seq) as i32);
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