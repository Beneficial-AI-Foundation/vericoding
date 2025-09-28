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
/* helper modified by LLM (iteration 5): change to use i8 instead of i32 */
fn compute_min_removals_impl(queries: &Vec<(char, i8)>, query_idx: usize) -> i8 {
    let mut left_positions = Vec::new();
    let mut right_positions = Vec::new();
    
    for i in 0..query_idx {
        let q = queries[i];
        if q.0 == 'L' {
            left_positions.push(q.1);
        } else if q.0 == 'R' {
            right_positions.push(q.1);
        }
    }
    
    let target_id = queries[query_idx].1;
    let mut left_conflicts = 0;
    let mut right_conflicts = 0;
    
    for pos in left_positions {
        if pos == target_id {
            left_conflicts += 1;
        }
    }
    
    for pos in right_positions {
        if pos == target_id {
            right_conflicts += 1;
        }
    }
    
    if left_conflicts > 0 && right_conflicts > 0 {
        left_conflicts + right_conflicts - 1
    } else {
        left_conflicts + right_conflicts
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
    /* code modified by LLM (iteration 5): remove unsupported map/collect, use i8 helper */
    let mut results = Vec::new();
    let mut i = 0;
    
    while i < queries.len()
        invariant
            0 <= (i as int) <= (queries.len() as int),
            results.len() == count_query_ops(queries@.map(|j: int, x: (char, i8)| (x.0, x.1 as int)).subrange(0, i as int)),
    {
        if queries[i].0 == '?' {
            let removals = compute_min_removals_impl(&queries, i);
            results.push(removals);
        }
        i += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}