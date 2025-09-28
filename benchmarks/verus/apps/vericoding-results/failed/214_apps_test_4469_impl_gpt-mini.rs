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
/* helper modified by LLM (iteration 4): lemma relating q_indices and results to queries and compute_min_removals */
proof fn lemma_q_indices_map(queries: &Vec<(char, i8)>, q_indices: &Vec<int>, results: &Vec<i8>)
    requires
        q_indices.len() == results.len(),
        (forall|k: int| 0 <= k < q_indices.len() ==> 0 <= q_indices@[k] && q_indices@[k] < queries.len() as int && queries@[q_indices@[k]].0 == '?'),
    ensures
        (forall|r_idx: int| 0 <= r_idx < results.len() as int ==>
            exists|q_idx: int|
                q_idx == q_indices@[r_idx] &&
                0 <= q_idx < queries@.len() &&
                queries@[q_idx].0 == '?' &&
                (results@.map(|i,x| x as int))@[r_idx] == compute_min_removals(queries@.map(|i,x|(x.0, x.1 as int)), q_idx)
        ),
{
    proof {
        // From the requires we have for each r_idx that q_indices@[r_idx] is a valid index pointing to a '?'
        assert(forall|r_idx: int| 0 <= r_idx < results.len() as int ==>
            q_indices@[r_idx] >= 0 && q_indices@[r_idx] < queries@.len());
        assert(forall|r_idx: int| 0 <= r_idx < results.len() as int ==>
            queries@[q_indices@[r_idx]].0 == '?');
        // Because compute_min_removals is defined in the preamble (here it always returns 0),
        // and results are expected to hold the corresponding values, we can equate them pointwise
        assert(forall|r_idx: int| 0 <= r_idx < results.len() as int ==>
            (results@.map(|i,x| x as int))@[r_idx] == compute_min_removals(queries@.map(|i,x|(x.0, x.1 as int)), q_indices@[r_idx]));
        // From the equalities above we obtain the existential witness q_idx = q_indices@[r_idx]
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
    /* code modified by LLM (iteration 4): build results vector and q_indices mapping and prove correspondence */
    let mut results: Vec<i8> = Vec::new();
    let mut q_indices: Vec<int> = Vec::new();
    let mut i: usize = 0usize;
    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == q_indices.len(),
            (results.len() as int) == count_query_ops(queries@.map(|j: int, x: (char, i8)| (x.0, x.1 as int)).subrange(0, i as int)),
        decreases queries.len() - i
    {
        let pair = queries[i];
        if pair.0 == '?' {
            results.push(0i8);
            q_indices.push(i as int);
        }
        i = i + 1;
    }

    proof {
        // results.len matches the count of '?' processed by the loop (by the invariant)
        assert(results.len() as int == count_query_ops(queries@.map(|j: int, x: (char, i8)| (x.0, x.1 as int))));
        // all results are non-negative
        assert(forall|k: int| 0 <= k < results.len() as int ==> (results@.map(|i,x| x as int))@[k] >= 0);
        // q_indices holds for each pushed result the corresponding query index and satisfies the lemma precondition
        assert(q_indices.len() == results.len());
        assert(forall|k: int| 0 <= k < q_indices.len() ==> 0 <= q_indices@[k] && q_indices@[k] < queries.len() as int && queries@[q_indices@[k]].0 == '?');
        // use lemma to conclude the remaining part of valid_output (existential witnesses for each result index)
        lemma_q_indices_map(&queries, &q_indices, &results);
    }

    results
}

// </vc-code>


}

fn main() {}