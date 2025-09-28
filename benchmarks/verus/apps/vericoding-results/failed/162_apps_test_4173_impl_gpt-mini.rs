// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_query(query: (int, int, int)) -> bool {
    query.0 > 0 && query.1 > 0 && query.2 > 0
}

spec fn min_cost_for_query(n: int, a: int, b: int) -> int
    recommends n > 0 && a > 0 && b > 0
{
    if n % 2 == 0 {
        if n * a <= (n / 2) * b { n * a } else { (n / 2) * b }
    } else {
        if n * a <= (n / 2) * b + a { n * a } else { (n / 2) * b + a }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute cost using i8 arithmetic */
fn compute_cost_from_i8(n: i8, a: i8, b: i8) -> i8 {
    if n % 2 == 0 {
        let cost1 = n * a;
        let cost2 = (n / 2) * b;
        if cost1 <= cost2 { cost1 } else { cost2 }
    } else {
        let cost1 = n * a;
        let cost2 = (n / 2) * b + a;
        if cost1 <= cost2 { cost1 } else { cost2 }
    }
}

/* helper modified by LLM (iteration 5): lemma relating i8 computation to spec min_cost_for_query */
fn lemma_compute_cost_matches_spec(n: i8, a: i8, b: i8)
    requires valid_query((n as int, a as int, b as int))
    ensures compute_cost_from_i8(n, a, b) as int == min_cost_for_query(n as int, a as int, b as int)
{
    proof {
        if n % 2 == 0 {
            let c1 = n * a;
            let c2 = (n / 2) * b;
            if c1 <= c2 {
                assert(compute_cost_from_i8(n, a, b) == c1);
                assert(min_cost_for_query(n as int, a as int, b as int) == (n as int) * (a as int));
                assert(c1 as int == (n as int) * (a as int));
            } else {
                assert(compute_cost_from_i8(n, a, b) == c2);
                assert(min_cost_for_query(n as int, a as int, b as int) == (n as int / 2) * (b as int));
                assert(c2 as int == (n as int / 2) * (b as int));
            }
        } else {
            let c1 = n * a;
            let c2 = (n / 2) * b + a;
            if c1 <= c2 {
                assert(compute_cost_from_i8(n, a, b) == c1);
                assert(min_cost_for_query(n as int, a as int, b as int) == (n as int) * (a as int));
                assert(c1 as int == (n as int) * (a as int));
            } else {
                assert(compute_cost_from_i8(n, a, b) == c2);
                assert(min_cost_for_query(n as int, a as int, b as int) == (n as int / 2) * (b as int) + (a as int));
                assert(c2 as int == (n as int / 2) * (b as int) + (a as int));
            }
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<(i8, i8, i8)>) -> (results: Vec<i8>)
    requires 
        forall|i: int| 0 <= i < queries@.len() ==> #[trigger] valid_query((queries@[i].0 as int, queries@[i].1 as int, queries@[i].2 as int))
    ensures 
        results@.len() == queries@.len() &&
        forall|i: int| 0 <= i < queries@.len() ==> {
            let n = queries@[i].0 as int;
            let a = queries@[i].1 as int;
            let b = queries@[i].2 as int;
            #[trigger] results@[i] as int == (if n % 2 == 0 {
                if n * a <= (n / 2) * b { n * a } else { (n / 2) * b }
            } else {
                if n * a <= (n / 2) * b + a { n * a } else { (n / 2) * b + a }
            })
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterate queries and compute costs using int loop and usize indexing */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i: int = 0;
    while i < queries@.len() as int
        invariant
            results@.len() == i as nat,
        decreases queries@.len() - results@.len()
    {
        let q = queries.get(i as usize).get_Some_0();
        let n = q.0;
        let a = q.1;
        let b = q.2;
        proof {
            lemma_compute_cost_matches_spec(n, a, b);
        }
        let r = compute_cost_from_i8(n, a, b);
        results.push(r);
        i = i + 1;
    }
    results
}

// </vc-code>


}

fn main() {}