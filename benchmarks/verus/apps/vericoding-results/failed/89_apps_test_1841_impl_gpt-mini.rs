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
/* helper modified by LLM (iteration 2): use v@ for spec-indexing in invariant */
fn vec_contains(v: &Vec<i8>, x: i8) -> bool {
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < v.len()
        invariant
            0 <= i as int && i as int <= v.len() as int,
            found ==> (exists|j: int| 0 <= j && j < i as int && v@[j] == x),
        decreases v.len() - i
    {
        if v[i] == x {
            found = true;
        }
        i += 1;
    }
    found
}

/* helper modified by LLM (iteration 2): maintain seen and count relation */
fn count_distinct(a: &Vec<i8>, start: usize) -> i8 {
    let mut seen: Vec<i8> = Vec::new();
    let mut i: usize = start;
    let mut count: i8 = 0;
    while i < a.len()
        invariant
            start <= i,
            i <= a.len(),
            count as int == seen.len() as int,
        decreases a.len() - i
    {
        let v = a[i];
        if !vec_contains(&seen, v) {
            seen.push(v);
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
{
    /* code modified by LLM (iteration 2): compute distinct counts per query using helpers */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < m as usize
        invariant
            i <= m as usize,
            result.len() == i,
        decreases (m as int) - (i as int)
    {
        let q: usize = queries[i] as usize;
        let start: usize = q - 1usize;
        let c: i8 = count_distinct(&a, start);
        result.push(c);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}