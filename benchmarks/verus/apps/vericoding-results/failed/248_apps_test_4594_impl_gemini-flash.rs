// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(diameters: Seq<int>) -> bool {
    diameters.len() > 0 && forall|i: int| 0 <= i < diameters.len() ==> diameters[i] > 0
}

spec fn num_distinct(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.subrange(1, s.len() as int).contains(s[0]) {
        num_distinct(s.subrange(1, s.len() as int))
    } else {
        1 + num_distinct(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [brief description] */
spec fn seq_contains(s: Seq<int>, val: int) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == val
}

// This spec fn helps to reason about the elements that have been processed.
spec fn distinct_elements_in_range(diameters_seq: Seq<int>, start: int, end: int) -> Seq<int>
    decreases end - start
{
    if start >= end {
        Seq::new()
    } else {
        let rest = distinct_elements_in_range(diameters_seq, start + 1, end);
        if rest.contains(diameters_seq[start]) {
            rest
        } else {
            rest.push(diameters_seq[start])
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(diameters: Vec<i8>) -> (result: i8)
    requires 
        valid_input(diameters@.map(|i, x| x as int)),
    ensures 
        result as int == num_distinct(diameters@.map(|i, x| x as int)),
        result as int >= 1,
        result as int <= diameters@.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): [brief description] */
{
    let mut distinct_count: i8 = 0;
    let mut seen: Seq<int> = Seq::new();
    let diameters_seq = diameters@.map(|i, x| x as int); // Create a ghost sequence for spec reasoning

    let mut i: usize = 0; // Use usize for indexing
    while (i as int) < diameters.len()
        invariant 
            0 <= (i as int) <= diameters.len(),
            distinct_count as int == seen.len(), // distinct_count represents actual elements in `seen`
            seen == distinct_elements_in_range(diameters_seq, 0, i as int),
            forall|k: int| 0 <= k < seen.len() ==> seq_contains(diameters_seq.subrange(0, i as int), seen[k]),
            forall|k: int, l: int| 0 <= k < seen.len() && 0 <= l < seen.len() && k != l ==> seen[k] != seen[l],
        decreases diameters.len() - (i as int)
    {
        let current_diameter_int: int = diameters[i] as int; // Cast i8 to int for ghost operations
        if !seq_contains(seen, current_diameter_int) {
            distinct_count = (distinct_count + 1) as i8;
            seen = seen.push(current_diameter_int);
        }
        i = i + 1;
    }
    distinct_count
}
// </vc-code>


}

fn main() {}