// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_building_params(n: int, h: int, a: int, b: int) -> bool {
    n >= 1 && h >= 1 && 1 <= a <= b <= h
}

spec fn valid_query(query: (int, int, int, int), n: int, h: int) -> bool {
    1 <= query.0 <= n && 1 <= query.1 <= h &&
    1 <= query.2 <= n && 1 <= query.3 <= h
}

spec fn valid_queries(queries: Seq<(int, int, int, int)>, n: int, h: int) -> bool {
    forall|i: int| 0 <= i < queries.len() ==> #[trigger] valid_query(queries[i], n, h)
}

spec fn min_travel_time(t1: int, f1: int, t2: int, f2: int, a: int, b: int) -> int {
    if t1 == t2 {
        if f1 >= f2 { f1 - f2 } else { f2 - f1 }
    } else if f1 >= a && f1 <= b {
        (if t2 >= t1 { t2 - t1 } else { t1 - t2 }) + (if f2 >= f1 { f2 - f1 } else { f1 - f2 })
    } else if f1 < a {
        (a - f1) + (if t2 >= t1 { t2 - t1 } else { t1 - t2 }) + (if f2 >= a { f2 - a } else { a - f2 })
    } else {
        (f1 - b) + (if t2 >= t1 { t2 - t1 } else { t1 - t2 }) + (if f2 >= b { f2 - b } else { b - f2 })
    }
}

spec fn correct_results(queries: Seq<(int, int, int, int)>, results: Seq<int>, a: int, b: int) -> bool {
    results.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> {
        let (t1, f1, t2, f2) = queries[i];
        #[trigger] results[i] == min_travel_time(t1, f1, t2, f2, a, b)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, h: i8, a: i8, b: i8, queries: Vec<(i8, i8, i8, i8)>) -> (results: Vec<i8>)
    requires
        valid_building_params(n as int, h as int, a as int, b as int),
        valid_queries(queries@.map_values(|x: (i8, i8, i8, i8)| (x.0 as int, x.1 as int, x.2 as int, x.3 as int)), n as int, h as int),
    ensures
        correct_results(queries@.map_values(|x: (i8, i8, i8, i8)| (x.0 as int, x.1 as int, x.2 as int, x.3 as int)), results@.map_values(|x: i8| x as int), a as int, b as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}