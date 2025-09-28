// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_composite(x: int) -> bool {
    x >= 4 && exists|k: int| 2 <= k < x && #[trigger] (x % k) == 0
}

spec fn valid_input(queries: Seq<int>) -> bool {
    forall|i: int| 0 <= i < queries.len() ==> queries[i] >= 1
}

spec fn max_composite_summands(n: int) -> int {
    if n % 4 == 0 {
        n / 4
    } else if n % 4 == 1 && n / 4 >= 2 {
        n / 4 - 1
    } else if n % 4 == 2 && n / 4 >= 1 {
        n / 4
    } else if n % 4 == 3 && n / 4 >= 3 {
        n / 4 - 1
    } else {
        -1
    }
}

spec fn valid_result(queries: Seq<int>, results: Seq<int>) -> bool {
    results.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> results[i] == max_composite_summands(queries[i]) &&
    forall|i: int| 0 <= i < queries.len() ==> results[i] >= -1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add lemma to prove max_composite_summands computation correctness with proper precondition check */
proof fn lemma_max_composite_summands_correct(n: int)
    requires n >= 1
    ensures
        max_composite_summands(n) == {
            if n % 4 == 0 {
                n / 4
            } else if n % 4 == 1 && n / 4 >= 2 {
                n / 4 - 1
            } else if n % 4 == 2 && n / 4 >= 1 {
                n / 4
            } else if n % 4 == 3 && n / 4 >= 3 {
                n / 4 - 1
            } else {
                -1
            }
        }
{
    // The lemma is proved by the definition
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i, x: i8| x as int))
    ensures valid_result(queries@.map(|i, x: i8| x as int), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix type annotation for Vec<i8> */
    let mut results: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == i,
            valid_input(queries@.map(|j, x: i8| x as int)),
            forall|j: int| 0 <= j < i ==> results@[j] == max_composite_summands(queries@[j] as int),
            forall|j: int| 0 <= j < i ==> results@[j] >= -1,
        decreases queries.len() - i
    {
        let query_val = queries[i];
        let n_exec = query_val as i32;
        let result = if n_exec % 4 == 0 {
            n_exec / 4
        } else if n_exec % 4 == 1 && n_exec / 4 >= 2 {
            n_exec / 4 - 1
        } else if n_exec % 4 == 2 && n_exec / 4 >= 1 {
            n_exec / 4
        } else if n_exec % 4 == 3 && n_exec / 4 >= 3 {
            n_exec / 4 - 1
        } else {
            -1
        };
        
        proof {
            let ghost n = query_val as int;
            assert(n >= 1);
            lemma_max_composite_summands_correct(n);
            assert(result as int == max_composite_summands(n));
            assert(result >= -1);
        }
        
        results.push(result as i8);
        i += 1;
    }
    
    proof {
        assert(results.len() == queries.len());
        assert(forall|j: int| 0 <= j < queries.len() ==> results@[j] == max_composite_summands(queries@[j] as int));
        assert(forall|j: int| 0 <= j < queries.len() ==> results@[j] >= -1);
    }
    
    results
}
// </vc-code>


}

fn main() {}