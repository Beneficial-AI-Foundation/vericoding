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
/* helper modified by LLM (iteration 5): totals_from_seq_helper computes (chest,biceps,back) from seq */
spec fn totals_from_seq_helper(s: Seq<int>, index: int) -> (int, int, int)
    decreases s.len()
{
    if s.len() == 0 {
        (0int, 0int, 0int)
    } else {
        let rest = s.subrange(1, s.len() as int);
        let (c, b, ba) = totals_from_seq_helper(rest, index + 1);
        if index % 3 == 0 {
            (s[0int] + c, b, ba)
        } else if index % 3 == 1 {
            (c, s[0int] + b, ba)
        } else {
            (c, b, s[0int] + ba)
        }
    }
}

/* helper modified by LLM (iteration 5): totals_from_seq wraps helper starting at index 0 */
spec fn totals_from_seq(s: Seq<int>) -> (int, int, int)
    decreases s.len()
{
    totals_from_seq_helper(s, 0int)
}

/* helper modified by LLM (iteration 5): proof relating spec totals to totals_from_seq */
proof fn totals_from_seq_matches_spec(s: Seq<int>)
    ensures
        chest_total(s) == (totals_from_seq(s)).0,
        biceps_total(s) == (totals_from_seq(s)).1,
        back_total(s) == (totals_from_seq(s)).2,
    decreases s.len()
{
    if s.len() == 0 {
        // base case: all totals are 0 by definitions
    } else {
        let rest = s.subrange(1, s.len() as int);
        totals_from_seq_matches_spec(rest);
        // The recursive definitions of chest_total / biceps_total / back_total
        // mirror totals_from_seq_helper, so unfolding and the inductive
        // hypothesis establish the equalities.
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
    /* code modified by LLM (iteration 5): compute runtime totals and relate them to spec totals using proofs without top-level ghost */
    let mut i: usize = 0usize;
    let mut chest_r: i64 = 0i64;
    let mut biceps_r: i64 = 0i64;
    let mut back_r: i64 = 0i64;
    while i < reps.len()
        invariant
            0 <= i as int <= reps.len() as int,
            chest_r as int == (totals_from_seq(reps@.map(|j: int, x: i8| x as int).subrange(0, i as int))).0,
            biceps_r as int == (totals_from_seq(reps@.map(|j: int, x: i8| x as int).subrange(0, i as int))).1,
            back_r as int == (totals_from_seq(reps@.map(|j: int, x: i8| x as int).subrange(0, i as int))).2,
        decreases reps.len() - i
    {
        let v: i8 = reps[i];
        if i % 3 == 0usize {
            chest_r = chest_r + (v as i64);
        } else if i % 3 == 1usize {
            biceps_r = biceps_r + (v as i64);
        } else {
            back_r = back_r + (v as i64);
        }
        i = i + 1usize;
    }

    proof {
        let s: Seq<int> = reps@.map(|j: int, x: i8| x as int);
        totals_from_seq_matches_spec(s);
        assert(chest_r as int == (totals_from_seq(s)).0);
        assert(biceps_r as int == (totals_from_seq(s)).1);
        assert(back_r as int == (totals_from_seq(s)).2);
    }

    if chest_r >= biceps_r && chest_r >= back_r {
        proof {
            assert(chest_r as int >= biceps_r as int);
            assert(chest_r as int >= back_r as int);
        }
        "chest"
    } else if biceps_r > chest_r && biceps_r >= back_r {
        proof {
            assert(biceps_r as int > chest_r as int);
            assert(biceps_r as int >= back_r as int);
        }
        "biceps"
    } else {
        proof {
            assert(back_r as int > chest_r as int);
            assert(back_r as int > biceps_r as int);
        }
        "back"
    }
}

// </vc-code>


}

fn main() {}