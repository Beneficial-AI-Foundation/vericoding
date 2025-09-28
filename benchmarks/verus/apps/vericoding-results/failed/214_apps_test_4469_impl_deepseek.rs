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
/* helper modified by LLM (iteration 5): fixed compilation errors and proper ghost code handling */
fn simulate_queries_body(queries: Seq<(char, int)>, query_idx: int) -> BookshelfState
    requires
        0 <= query_idx < queries.len(),
        valid_input(queries)
    ensures
        result.positions.dom().finite(),
        forall|pos: int| result.positions.contains(pos) ==> result.positions[pos] >= 0,
        result.head >= 0,
        result.tail >= 0,
        result.head <= result.tail
{
    proof {
        let mut state = BookshelfState {
            positions: Map::empty(),
            head: 0,
            tail: 0,
        };
        
        for i in 0..query_idx
            invariant
                0 <= i <= query_idx,
                state.positions.dom().finite(),
                forall|pos: int| state.positions.contains(pos) ==> state.positions[pos] >= 0,
                state.head >= 0,
                state.tail >= 0,
                state.head <= state.tail
            decreases query_idx - i
        {
            let query = queries[i];
            if query.0 == 'L' {
                let new_pos = state.head - 1;
                state.head = new_pos;
                state.positions = state.positions.insert(query.1, new_pos);
            } else if query.0 == 'R' {
                let new_pos = state.tail;
                state.tail = new_pos + 1;
                state.positions = state.positions.insert(query.1, new_pos);
            }
        }
        state
    }
}

fn compute_min_removals_correct(queries: Seq<(char, int)>, query_idx: int) -> int
    requires
        0 <= query_idx < queries.len(),
        queries[query_idx].0 == '?',
        valid_input(queries)
    ensures
        result >= 0,
        result <= queries.len()
{
    proof {
        let state_before = simulate_queries_body(queries, query_idx);
        let target_book = queries[query_idx].1;
        assert(state_before.positions.contains(target_book));
        let book_pos = state_before.positions[target_book];
        let left_books = book_pos - state_before.head;
        let right_books = state_before.tail - book_pos - 1;
        if left_books < right_books {
            left_books
        } else {
            right_books
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<(char, i8)>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int)))
    ensures valid_output(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int)), results@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed variable scoping and ghost conversion */
    let queries_int = queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int));
    let mut results: Vec<i8> = Vec::new();
    let mut result_idx = 0;
    
    for q_idx in 0..queries_int.len()
        invariant
            0 <= result_idx,
            results@.len() == result_idx,
            forall|i: int| 0 <= i < result_idx ==> results@[i] >= 0,
            valid_input(queries_int)
        decreases queries_int.len() - q_idx
    {
        let query = queries_int[q_idx];
        if query.0 == '?' {
            proof {
                let ghost min_removals = compute_min_removals_correct(queries_int, q_idx);
                results.push(min_removals as i8);
                result_idx += 1;
            }
        }
    }
    
    results
}
// </vc-code>


}

fn main() {}