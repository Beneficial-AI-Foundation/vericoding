// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn all_even(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] % 2 == 0
}

spec fn has_odd(a: Seq<int>) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate has_odd on mapped seq to Vec indexing */
spec fn vec_has_odd_equiv(a: &Vec<i8>) -> bool {
    has_odd(a@.map(|i: int, x: i8| x as int)) <==> exists|j: int| 0 <= j < a.len() && (a@[j] as int) % 2 == 1
}

/* helper modified by LLM (iteration 5): relate all_even on mapped seq to Vec indexing */
spec fn vec_all_even_equiv(a: &Vec<i8>) -> bool {
    all_even(a@.map(|i: int, x: i8| x as int)) <==> forall|j: int| 0 <= j < a.len() ==> (a@[j] as int) % 2 == 0
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: &'static str)
    ensures 
        (result == "Second") <==> all_even(a@.map(|i: int, x: i8| x as int)),
        (result == "First") <==> has_odd(a@.map(|i: int, x: i8| x as int)),
        result == "First" || result == "Second",
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate to detect any odd element with invariant proof */
    let mut i: usize = 0;
    let mut seen_odd: bool = false;

    while i < a.len()
        invariant
            i <= a.len(),
            seen_odd <==> exists|j: int| 0 <= j < i as int && (a@[j] as int) % 2 == 1,
        decreases a.len() - i
    {
        let idx = i;
        let cur: i8 = a[idx];

        proof {
            // invariant holds at start of iteration for idx
            assert(seen_odd <==> exists|j: int| 0 <= j < idx as int && (a@[j] as int) % 2 == 1);
        }

        if (cur as int) % 2 == 1 {
            seen_odd = true;
        }
        i = idx + 1;

        proof {
            // Re-establish invariant for new i (idx + 1)
            // Case analysis on seen_odd after update
            if seen_odd {
                // If current element is odd, witness idx; otherwise witness from old invariant
                if (cur as int) % 2 == 1 {
                    assert(0 <= idx as int && idx as int < i as int);
                    assert((a@[idx] as int) % 2 == 1);
                    assert(exists|j: int| 0 <= j < i as int && (a@[j] as int) % 2 == 1);
                } else {
                    // not cur odd, so must have been seen before
                    assert(exists|j: int| 0 <= j < idx as int && (a@[j] as int) % 2 == 1);
                    assert(exists|j: int| 0 <= j < i as int && (a@[j] as int) % 2 == 1);
                }
            } else {
                // seen_odd is false: old invariant gives no witness below idx, and cur is not odd
                assert(!(exists|j: int| 0 <= j < idx as int && (a@[j] as int) % 2 == 1));
                assert((cur as int) % 2 != 1);
                assert(!(exists|j: int| 0 <= j < i as int && (a@[j] as int) % 2 == 1));
            }
        }
    }

    let result: &str = if seen_odd { "First" } else { "Second" };

    proof {
        // relate seen_odd over full array to has_odd on the mapped sequence
        assert(seen_odd <==> exists|j: int| 0 <= j < a.len() && (a@[j] as int) % 2 == 1);
        assert(has_odd(a@.map(|i: int, x: i8| x as int)) <==> exists|j: int| 0 <= j < a.len() && (a@[j] as int) % 2 == 1);
        assert(all_even(a@.map(|i: int, x: i8| x as int)) <==> forall|j: int| 0 <= j < a.len() ==> (a@[j] as int) % 2 == 0);
        if seen_odd {
            assert(result == "First");
            assert(has_odd(a@.map(|i: int, x: i8| x as int)));
        } else {
            assert(result == "Second");
            assert(all_even(a@.map(|i: int, x: i8| x as int)));
        }
    }

    result
}
// </vc-code>


}

fn main() {}