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
/* helper modified by LLM (iteration 5): fixed compilation error by changing `lemma` to `proof fn` */
proof fn lemma_count_query_ops_append(q1: Seq<(char, int)>, q2: Seq<(char, int)>)
    ensures count_query_ops(q1 + q2) == count_query_ops(q1) + count_query_ops(q2),
    decreases q1.len()
{
    if q1.len() > 0 {
        lemma_count_query_ops_append(q1.subrange(1, q1.len() as int), q2);
    }
}

/* helper modified by LLM (iteration 5): fixed compilation error by changing `lemma` to `proof fn` and removing trailing comma */
proof fn lemma_count_query_ops_subrange(queries: Seq<(char, int)>, i: int)
    requires 0 <= i < queries.len(),
    ensures
        count_query_ops(queries.subrange(0, i + 1)) ==
            count_query_ops(queries.subrange(0, i)) + (if queries[i].0 == '?' { 1 } else { 0 })
{
    let prefix = queries.subrange(0, i);
    let singleton = queries.subrange(i, i + 1);
    assert(queries.subrange(0, i + 1) === prefix + singleton);
    lemma_count_query_ops_append(prefix, singleton);
    assert(singleton.len() == 1);
    assert(singleton[0] === queries[i]);
    assert(count_query_ops(singleton) == (if queries[i].0 == '?' { 1 } else { 0 }));
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<(char, i8)>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int)))
    ensures valid_output(queries@.map(|i: int, x: (char, i8)| (x.0, x.1 as int)), results@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): addressing compilation error in helpers */
    ghost let spec_queries = queries@.map(|_idx: int, x: (char, i8)| (x.0, x.1 as int));

    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            valid_input(spec_queries),
            (results@.map(|_idx: int, x: i8| x as int)).len() as int == count_query_ops(spec_queries.subrange(0, i as int)),
            forall|j: int| 0 <= j < (results@.map(|_idx: int, x: i8| x as int)).len() ==> (results@.map(|_idx: int, x: i8| x as int))@[j] == 0,
        decreases queries.len() - i
    {
        proof {
            if i < queries.len() {
                lemma_count_query_ops_subrange(spec_queries, i as int);
            }
        }

        let q = queries[i];
        if q.0 == '?' {
            results.push(0i8);
        }

        i = i + 1;
    }

    results
}
// </vc-code>


}

fn main() {}