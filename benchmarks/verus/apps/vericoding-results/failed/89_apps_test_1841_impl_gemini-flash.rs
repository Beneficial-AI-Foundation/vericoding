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
/* code modified by LLM (iteration 5): Fixed a syntax error in the while loop's invariant block. */
{
    let mut distinct_counts: Vec<i8> = Vec::new();
    let mut cache: Vec<i8> = Vec::new();
    cache.resize(n as usize + 1, 0);

    let mut current_distinct_count: i8 = 0;
    let mut last_seen_index: Vec<i8> = Vec::new();
    last_seen_index.resize(101, -1); // Assuming values are between 1 and 100

    let a_int = a@.map(|idx, x| x as int);

    let mut i = n - 1;
    while i >= 0
        invariant
            0 <= i + 1 <= n,
            cache.len() == n as usize + 1,
            (forall |k: int| i + 1 <= k < n ==> cache[k as usize] as int == distinct_count(a_int, k)),
            current_distinct_count as int == distinct_count(a_int, i as int + 1),
            last_seen_index.len() == 101,
            (forall |val_idx: int| 0 <= val_idx < 101 ==> 
                (last_seen_index[val_idx as usize] == -1 || 
                 (i as int < last_seen_index[val_idx as usize] as int && last_seen_index[val_idx as usize] as int < n as int &&
                  a@[last_seen_index[val_idx as usize] as usize] == val_idx as i8)))

    {
        let val = a@[i as usize];
        if last_seen_index[val as usize] == -1 {
            current_distinct_count = current_distinct_count + 1;
        } else {
            proof {
                assert(last_seen_index[val as usize] as int > i as int);
            }
        }

        last_seen_index.set(val as usize, i);
        cache.set(i as usize, current_distinct_count);
        i = i - 1;
    }

    let m_usize = m as usize;
    distinct_counts.reserve(m_usize);
    let queries_int = queries@.map(|idx, x| x as int);

    let mut j = 0;
    while j < m
        invariant
            0 <= j <= m,
            distinct_counts.len() == j as usize,
            distinct_counts.capacity() == m_usize,
            cache.len() == n as usize + 1,
            (forall |k: int| 0 <= k < n ==> cache[k as usize] as int == distinct_count(a_int, k)),
            queries.len() == m,
            queries_int.len() == m
    {
        let query_val = queries@[j as usize]; // Use i8 for queries
        let query_idx = (query_val - 1) as usize; // Cast to usize directly
        distinct_counts.push(cache[query_idx]);
        j = j + 1;
    }

    distinct_counts
}
// </vc-code>


}

fn main() {}