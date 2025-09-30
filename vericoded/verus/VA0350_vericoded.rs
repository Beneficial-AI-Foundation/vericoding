// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(queries: Seq<int>) -> bool {
    forall|i: int| 0 <= i < queries.len() ==> queries[i] >= 2
}

spec fn min_additional_matches(n: int) -> int
    recommends n >= 2
{
    if n >= 4 { n % 2 } else { 4 - n }
}

spec fn valid_result(queries: Seq<int>, results: Seq<int>) -> bool
    recommends valid_input(queries)
{
    results.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> results[i] == min_additional_matches(queries[i])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i: int, x: i8| x as int))
    ensures valid_result(queries@.map(|i: int, x: i8| x as int), results@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut results = Vec::new();
    let mut i = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            results.len() == i,
            valid_input(queries@.map(|j: int, x: i8| x as int)),
            forall|j: int| 0 <= j < i ==> results@[j] as int == min_additional_matches(queries@[j] as int)
        decreases queries.len() - i
    {
        let n = queries[i];
        
        proof {
            assert(queries@.map(|j: int, x: i8| x as int)[i as int] == n as int);
            assert(n as int >= 2);
        }
        
        let result = if n >= 4 {
            (n % 2) as i8
        } else {
            (4 - n) as i8
        };
        
        proof {
            assert(result as int == min_additional_matches(n as int));
        }
        
        results.push(result);
        
        proof {
            assert(results@[i as int] as int == min_additional_matches(queries@[i as int] as int));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(results.len() == queries.len());
        assert(forall|j: int| 0 <= j < queries.len() ==> results@[j] as int == min_additional_matches(queries@[j] as int));
    }
    
    results
}
// </vc-code>


}

fn main() {}