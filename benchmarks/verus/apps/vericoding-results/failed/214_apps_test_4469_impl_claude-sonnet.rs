// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(queries: Seq<(char, int)>) -> bool {
    &&& queries.len() > 0
    &&& (forall|i: int| 0 <= i < queries.len() ==> queries[i].0 == 'L' || queries[i].0 == 'R' || queries[i].0 == '?')
    &&& (forall|i: int| 0 <= i < queries.len() ==> queries[i].1 > 0)
    &&& (forall|i: int, j: int| 0 <= i < j < queries.len() && (queries[i].0 == 'L' || queries[i].0 == 'R') && (queries[j].0 == 'L' || queries[j].0 == 'R') ==> queries[i].1 != queries[j].1)
    &&& (forall|i: int| 0 <= i < queries.len() && queries[i].0 == '?' ==> 
        exists|j: int| 0 <= j < i && (queries[j].0 == 'L' || queries[j].0 == 'R') && queries[j].1 == queries[i].1)
    &&& (exists|i: int| 0 <= i < queries.len() && queries[i].0 == '?')
}

spec fn count_query_ops(queries: Seq<(char, int)>) -> int
    decreases queries.len()
{
    if queries.len() == 0 {
        0
    } else {
        let head = queries[0];
        let tail = queries.subrange(1, queries.len() as int);
        if head.0 == '?' {
            1 + count_query_ops(tail)
        } else {
            count_query_ops(tail)
        }
    }
}

spec fn valid_output(queries: Seq<(char, int)>, results: Seq<int>) -> bool {
    &&& results.len() == count_query_ops(queries)
    &&& (forall|i: int| 0 <= i < results.len() ==> results[i] >= 0)
    &&& (forall|r_idx: int| #[trigger] results[r_idx] == compute_min_removals(queries, r_idx) ==> 0 <= r_idx < results.len() ==> 
        (exists|q_idx: int| 0 <= q_idx < queries.len() && queries[q_idx].0 == '?' &&
         results[r_idx] == compute_min_removals(queries, q_idx)))
    &&& (forall|q_idx: int| #[trigger] queries[q_idx] == queries[q_idx] ==> 0 <= q_idx < queries.len() && queries[q_idx].0 == '?' ==>
        (exists|r_idx: int| 0 <= r_idx < results.len() &&
         results[r_idx] == compute_min_removals(queries, q_idx)))
}

struct BookshelfState {
    positions: Map<int, int>,
    head: int,
    tail: int,
}

spec fn simulate_queries(queries: Seq<(char, int)>, query_idx: int) -> BookshelfState {
    BookshelfState {
        positions: Map::empty(),
        head: 0,
        tail: 0,
    }
}

spec fn compute_min_removals(queries: Seq<(char, int)>, query_idx: int) -> int {
    0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added explicit type annotation for Vec */
spec fn simulate_queries_impl(queries: Seq<(char, int)>, end_idx: int) -> BookshelfState
    requires 0 <= end_idx <= queries.len()
    decreases end_idx
{
    if end_idx == 0 {
        BookshelfState {
            positions: Map::empty(),
            head: 0,
            tail: 0,
        }
    } else {
        let prev_state = simulate_queries_impl(queries, end_idx - 1);
        let query = queries[end_idx - 1];
        if query.0 == 'L' {
            BookshelfState {
                positions: prev_state.positions.insert(query.1, prev_state.head),
                head: prev_state.head - 1,
                tail: prev_state.tail,
            }
        } else if query.0 == 'R' {
            BookshelfState {
                positions: prev_state.positions.insert(query.1, prev_state.tail),
                head: prev_state.head,
                tail: prev_state.tail + 1,
            }
        } else {
            prev_state
        }
    }
}

spec fn count_removals(state: BookshelfState, book_id: int, target_pos: int) -> int {
    if state.positions.contains_key(book_id) {
        let book_pos = state.positions[book_id];
        if book_pos < target_pos {
            target_pos - book_pos
        } else {
            book_pos - target_pos
        }
    } else {
        0
    }
}

fn count_queries_exec(queries: &Vec<(char, i8)>) -> (count: usize)
    requires valid_input(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int)))
    ensures count as int == count_query_ops(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int)))
{
    let mut count = 0usize;
    let mut i = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            count <= i,
            count as int == count_query_ops(queries@.map(|j: int, x: (char, i8)| (x.0, x.1 as int)).subrange(0, i as int)),
        decreases queries.len() - i
    {
        if queries[i].0 == '?' {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<(char, i8)>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int)))
    ensures valid_output(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int)), results@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type annotation for Vec */
    let query_count = count_queries_exec(&queries);
    let mut results: Vec<i8> = Vec::with_capacity(query_count);
    let mut query_idx = 0;
    let mut result_idx = 0;
    
    while query_idx < queries.len()
        invariant
            0 <= query_idx <= queries.len(),
            result_idx <= query_count,
            results.len() == result_idx,
            result_idx as int == count_query_ops(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int)).subrange(0, query_idx as int)),
            valid_input(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int))),
            forall|i: int| 0 <= i < results.len() ==> results@[i] >= 0,
        decreases queries.len() - query_idx
    {
        let query = queries[query_idx];
        if query.0 == '?' {
            let min_removals = 0i8;
            results.push(min_removals);
            result_idx = result_idx + 1;
        }
        query_idx = query_idx + 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}