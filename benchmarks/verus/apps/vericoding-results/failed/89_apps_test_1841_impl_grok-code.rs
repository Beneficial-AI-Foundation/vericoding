// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: Seq<int>, queries: Seq<int>) -> bool {
    a.len() == n && queries.len() == m && n >= 1 && m >= 1 &&
    forall|i: int| 0 <= i < m ==> (#[trigger] queries[i], 1 <= queries[i] <= n).1
}

spec fn distinct_count(a: Seq<int>, start: int) -> int
    recommends 0 <= start < a.len()
{
    let suffix_indices = Set::new(|j: int| start <= j < a.len());
    let suffix_values = suffix_indices.map(|j: int| a[j]);
    suffix_values.len() as int
}
// </vc-preamble>

// <vc-helpers>
const MAX: usize = 256;

spec fn distinct_count_from_to(a: Seq<int>, start: int, end: int) -> int
    recommends
        0 <= start <= end <= a.len()
{
    let subseq = a.subrange(start, end);
    Set::<int>::empty().add_seq(&subseq).len() as int
}

/* helper modified by LLM (iteration 5): Fixed return type for distinct_in_suffix_exec */

pub fn distinct_in_suffix_exec(a: &Vec<i8>, start: usize) -> (result: usize)
    requires
        start <= a.len()
    ensures
        result as int == distinct_count(a@.map(|i, x| x as int), start as int)
{
    let mut seen: Vec<bool> = Vec::with_capacity(MAX);
    seen.resize(MAX, false);
    let mut count: usize = 0;
    let mut i: usize = start;
    while i < a.len()
        invariant
            count as int == distinct_count_from_to(a@.map(|i, x| x as int), start as int, i as int),
            i >= start,
            i <= a.len()
        decreases a.len() - i
    {
        let val = a[i];
        let idx = (val as i32 + 128) as usize;
        if !seen[idx] {
            seen[idx] = true;
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, m as int, a@.map(|i, x| x as int), queries@.map(|i, x| x as int))
    ensures 
        result.len() == m &&
        (forall|i: int| 0 <= i < m ==> (#[trigger] result@[i], result@[i] as int == distinct_count(a@.map(|i, x| x as int), queries@[i] as int - 1)).1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implemented solve function */
{
    let mut result: Vec<i8> = Vec::new();
    for qi in 0..(m as usize) {
        let start = (queries[qi] - 1) as usize;
        let count = distinct_in_suffix_exec(&a, start) as i8;
        result.push(count);
    }
    result
}
// </vc-code>


}

fn main() {}