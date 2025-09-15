// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
fn count_occurrences_exec(xs: &Vec<i32>, target: i32) -> i64 {
    let mut count: i64 = 0;
    for i in 0..xs.len() {
        if xs[i] == target {
            count += 1;
        }
    }
    count
}

proof fn lemma_count_occurrences_exec_correct(xs: Vec<i32>, target: i32)
    ensures
        count_occurrences(xs@, target) == count_occurrences_exec(&xs, target) as nat
/* helper modified by LLM (iteration 3): Implemented the proof body to connect spec and exec counts using ghost loop */
{
    let mut count_ghost: nat = 0;
    let mut i: int = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            count_ghost == count_occurrences(xs@.subrange(0, i), target)
        decreases xs.len() - i
    {
        if xs@[i] == target {
            count_ghost = count_ghost + 1;
        }
        i = i + 1;
    }
    assert(count_ghost == count_occurrences(xs@, target));
}
// </vc-helpers>

// <vc-spec>
fn most_frequent(xs: Vec<i32>) -> (result: i32)
    requires xs.len() > 0,
    ensures
        xs@.contains(result),
        forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= count_occurrences(xs@, result),
        exists|first_idx: int| 
            0 <= first_idx < xs.len() && 
            xs[first_idx] == result && 
            count_occurrences(xs@, result) == count_occurrences(xs@, xs[first_idx]) &&
            forall|i: int| 0 <= i < first_idx ==> count_occurrences(xs@, xs[i]) < count_occurrences(xs@, result),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed compilation errors by removing invalid 'take' and passing correct arguments */
    let mut max_count: i64 = 0;
    let mut index: usize = 0;
    for i in 0..xs.len() {
        proof {
            lemma_count_occurrences_exec_correct(xs, xs[i]);
        }
        let current_count = count_occurrences_exec(&xs, xs[i]);
        if current_count > max_count {
            max_count = current_count;
            index = i;
        }
    }
    xs[index]
}
// </vc-code>

}
fn main() {}