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

proof fn distinct_count_monotonic_lemma(a: Seq<int>, start1: int, start2: int)
    requires
        0 <= start2 <= start1 < a.len(),
    ensures
        distinct_count(a, start2) >= distinct_count(a, start1),
{
}

fn compute_distinct_count(a: Vec<i8>, start: usize) -> (count: i8)
    requires
        start < a.len(),
    ensures
        count as int == distinct_count(a@.map(|i, x| x as int), start as int),
        count >= 0,
decreases a.len() - start
{
    /* helper modified by LLM (iteration 5): Fix type conversion in verification */
    let mut seen = std::collections::HashSet::new();
    let mut count = 0;
    let mut i = start;
    
    while i < a.len()
        invariant
            i >= start,
            i <= a.len(),
            count as int == distinct_count(a@.map(|i, x| x as int), i as int),
            count >= 0,
        decreases a.len() - i
    {
        if !seen.contains(&a[i]) {
            seen.insert(a[i]);
            count = count + 1;
        }
        i = i + 1;
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
    /* code modified by LLM (iteration 5): Fix type conversion in bounds checking */
    let mut result = Vec::with_capacity(m as usize);
    let mut distinct_counts = Vec::new();
    
    let n_usize = n as usize;
    
    for i in 0..n_usize {
        proof {
            assert(i < a.len());
        }
        let count = compute_distinct_count(a.clone(), i);
        distinct_counts.push(count);
    }
    
    let m_usize = m as usize;
    for i in 0..m_usize {
        proof {
            assert(i < queries.len());
            assert(1 <= queries[i] as int && queries[i] as int <= n as int);
        }
        let query_val = queries[i];
        let query_index = (query_val as usize) - 1;
        result.push(distinct_counts[query_index]);
    }
    
    result
}
// </vc-code>


}

fn main() {}