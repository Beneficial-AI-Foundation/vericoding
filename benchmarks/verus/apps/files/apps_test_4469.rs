// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(queries: Seq<(char, int)>) -> bool {
    &&& queries.len() > 0
    &&& (forall|i: int| 0 <= i < queries.len() ==> queries[i].0 == 'L' || queries[i].0 == 'R' || queries[i].0 == '?')
    &&& (forall|i: int| 0 <= i < queries.len() ==> queries[i].1 > 0)
    &&& (forall|i: int, j: int| 0 <= i < j < queries.len() && (queries[i].0 == 'L' || queries[i].0 == 'R') && (queries[j].0 == 'L' || queries[j].0 == 'R') ==> queries[i].1 != queries[j].1)
    &&& (forall|i: int| 0 <= i < queries.len() && queries[i].0 == '?' ==> 
        exists|j: int| 0 <= j < i && (queries[j].0 == 'L' || queries[j].0 == 'R') && queries[j].1 == queries[i].1)
    &&& (exists|i: int| 0 <= i < queries.len() && queries[i].0 == '?')
}

spec fn count_query_queries(queries: Seq<(char, int)>) -> nat
    decreases queries.len()
{
    if queries.len() == 0 {
        0nat
    } else {
        let last_is_query: nat = if queries[queries.len() - 1].0 == '?' { 1nat } else { 0nat };
        count_query_queries(queries.subrange(0, queries.len() - 1)) + last_is_query
    }
}

spec fn valid_output(queries: Seq<(char, int)>, results: Seq<int>) -> bool {
    &&& results.len() == count_query_queries(queries)
    &&& (forall|i: int| 0 <= i < results.len() ==> results[i] >= 0)
    &&& (forall|r_idx: int| 0 <= r_idx < results.len() ==> 
        exists|q_idx: int| 0 <= q_idx < queries.len() && queries[q_idx].0 == '?' &&
         results[r_idx] == compute_min_removals(queries, q_idx))
    &&& (forall|q_idx: int| 0 <= q_idx < queries.len() && queries[q_idx].0 == '?' ==>
        exists|r_idx: int| 0 <= r_idx < results.len() &&
         results[r_idx] == compute_min_removals(queries, q_idx))
}

struct BookshelfState {
    positions: Map<int, int>,
    head: int,
    tail: int,
}

spec fn simulate_queries(queries: Seq<(char, int)>, query_idx: int) -> BookshelfState {
    /* TODO: Implement simulation logic */
    BookshelfState {
        positions: Map::empty(),
        head: 0,
        tail: 0,
    }
}

spec fn compute_min_removals(queries: Seq<(char, int)>, query_idx: int) -> int {
    let book_id = queries[query_idx].1;
    let state = simulate_queries(queries, query_idx);
    let pos = state.positions[book_id];
    let left_removals = pos - state.head;
    let right_removals = state.tail - pos;
    let min_removals = if left_removals <= right_removals { left_removals } else { right_removals };
    min_removals - 1
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Seq<(char, int)>) -> (results: Seq<int>)
    requires valid_input(queries)
    ensures valid_output(queries, results)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Seq::empty()
}
// </vc-code>


}

fn main() {}