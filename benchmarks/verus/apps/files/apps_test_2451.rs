// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_building_params(n: int, h: int, a: int, b: int) -> bool {
    n >= 1 && h >= 1 && 1 <= a && a <= b && b <= h
}

spec fn valid_query(query: (int, int, int, int), n: int, h: int) -> bool {
    1 <= query.0 && query.0 <= n && 1 <= query.1 && query.1 <= h &&
    1 <= query.2 && query.2 <= n && 1 <= query.3 && query.3 <= h
}

spec fn valid_queries(queries: Seq<(int, int, int, int)>, n: int, h: int) -> bool {
    forall|i: int| 0 <= i < queries.len() ==> valid_query(queries[i], n, h)
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn min_travel_time(t1: int, f1: int, t2: int, f2: int, a: int, b: int) -> int {
    if t1 == t2 {
        abs(f1 - f2)
    } else if f1 >= a && f1 <= b {
        abs(t2 - t1) + abs(f2 - f1)
    } else if f1 < a {
        abs(a - f1) + abs(t2 - t1) + abs(f2 - a)
    } else {
        abs(b - f1) + abs(t2 - t1) + abs(f2 - b)
    }
}

spec fn correct_results(queries: Seq<(int, int, int, int)>, results: Seq<int>, a: int, b: int) -> bool {
    results.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> {
        let (t1, f1, t2, f2) = queries[i];
        results[i] == min_travel_time(t1, f1, t2, f2, a, b)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, h: int, a: int, b: int, queries: Seq<(int, int, int, int)>) -> (results: Seq<int>)
    requires 
        valid_building_params(n, h, a, b),
        valid_queries(queries, n, h),
    ensures correct_results(queries, results, a, b)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}