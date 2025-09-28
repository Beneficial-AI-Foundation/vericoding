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
/* helper modified by LLM (iteration 4): trivial helper asserting true */
spec fn helper_true() -> bool {
    true
}
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
    /* code modified by LLM (iteration 4): compute travel times directly in the loop and prove each result equals the spec min_travel_time */
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            0 <= i as int <= queries.len() as int,
            results@.len() == i as int,
            forall|j: int| 0 <= j && j < i as int ==> 
                results@[j] as int == min_travel_time((queries@[j]).0 as int, (queries@[j]).1 as int, (queries@[j]).2 as int, (queries@[j]).3 as int, a as int, b as int),
        decreases queries.len() as int - i as int
    {
        let (t1, f1, t2, f2) = queries[i];
        let tt: i8 = if t1 == t2 {
            if f1 >= f2 { f1 - f2 } else { f2 - f1 }
        } else if f1 >= a && f1 <= b {
            let dt: i8 = if t2 >= t1 { t2 - t1 } else { t1 - t2 };
            let df: i8 = if f2 >= f1 { f2 - f1 } else { f1 - f2 };
            dt + df
        } else if f1 < a {
            let dt: i8 = if t2 >= t1 { t2 - t1 } else { t1 - t2 };
            (a - f1) + dt + (if f2 >= a { f2 - a } else { a - f2 })
        } else {
            let dt: i8 = if t2 >= t1 { t2 - t1 } else { t1 - t2 };
            (f1 - b) + dt + (if f2 >= b { f2 - b } else { b - f2 })
        };
        results.push(tt);
        proof {
            assert(results@.len() == i as int + 1);
            assert(results@[i as int] as int == tt as int);
            let tt_int: int = tt as int;
            if t1 == t2 {
                if f1 >= f2 {
                    assert(tt_int == f1 as int - f2 as int);
                    assert(tt_int == min_travel_time(t1 as int, f1 as int, t2 as int, f2 as int, a as int, b as int));
                } else {
                    assert(tt_int == f2 as int - f1 as int);
                    assert(tt_int == min_travel_time(t1 as int, f1 as int, t2 as int, f2 as int, a as int, b as int));
                }
            } else if f1 >= a && f1 <= b {
                assert(tt_int == (if t2 as int >= t1 as int { t2 as int - t1 as int } else { t1 as int - t2 as int }) + (if f2 as int >= f1 as int { f2 as int - f1 as int } else { f1 as int - f2 as int }));
                assert(tt_int == min_travel_time(t1 as int, f1 as int, t2 as int, f2 as int, a as int, b as int));
            } else if f1 < a {
                assert(tt_int == (a as int - f1 as int) + (if t2 as int >= t1 as int { t2 as int - t1 as int } else { t1 as int - t2 as int }) + (if f2 as int >= a as int { f2 as int - a as int } else { a as int - f2 as int }));
                assert(tt_int == min_travel_time(t1 as int, f1 as int, t2 as int, f2 as int, a as int, b as int));
            } else {
                assert(tt_int == (f1 as int - b as int) + (if t2 as int >= t1 as int { t2 as int - t1 as int } else { t1 as int - t2 as int }) + (if f2 as int >= b as int { f2 as int - b as int } else { b as int - f2 as int }));
                assert(tt_int == min_travel_time(t1 as int, f1 as int, t2 as int, f2 as int, a as int, b as int));
            }
        }
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}