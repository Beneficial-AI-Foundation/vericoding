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
/* helper modified by LLM (iteration 5): fixed preconditions and added overflow checks */
fn abs_diff(x: i8, y: i8) -> (result: i8)
    requires
        -128 <= x <= 127,
        -128 <= y <= 127,
        x >= y ==> x - y <= 127,
        y > x ==> y - x <= 127,
    ensures
        result as int == if x >= y { (x - y) as int } else { (y - x) as int },
{
    if x >= y { x - y } else { y - x }
}

fn compute_min_travel_time(t1: i8, f1: i8, t2: i8, f2: i8, a: i8, b: i8) -> (result: i8)
    requires
        1 <= t1 <= 127,
        1 <= f1 <= 127,
        1 <= t2 <= 127,
        1 <= f2 <= 127,
        1 <= a <= b <= 127,
        f1 < a ==> a - f1 <= 127,
        f1 > b ==> f1 - b <= 127,
    ensures
        result as int == min_travel_time(t1 as int, f1 as int, t2 as int, f2 as int, a as int, b as int),
{
    if t1 == t2 {
        abs_diff(f1, f2)
    } else if f1 >= a && f1 <= b {
        let dt = abs_diff(t1, t2);
        let df = abs_diff(f1, f2);
        dt + df
    } else if f1 < a {
        let dt = abs_diff(t1, t2);
        let df2a = abs_diff(f2, a);
        (a - f1) + dt + df2a
    } else {
        let dt = abs_diff(t1, t2);
        let df2b = abs_diff(f2, b);
        (f1 - b) + dt + df2b
    }
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
    /* code modified by LLM (iteration 5): fixed overflow checks in inline arithmetic */
    let mut results = Vec::new();
    let mut i = 0;
    
    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let (t1, f1, t2, f2) = queries@[j];
                #[trigger] results@[j] == min_travel_time(t1 as int, f1 as int, t2 as int, f2 as int, a as int, b as int)
            },
        decreases queries.len() - i
    {
        let (t1, f1, t2, f2) = queries[i];
        
        let travel_time = if t1 == t2 {
            abs_diff(f1, f2)
        } else if f1 >= a && f1 <= b {
            let dt = abs_diff(t1, t2);
            let df = abs_diff(f1, f2);
            dt + df
        } else if f1 < a {
            let dt = abs_diff(t1, t2);
            let df2a = abs_diff(f2, a);
            (a - f1) + dt + df2a
        } else {
            let dt = abs_diff(t1, t2);
            let df2b = abs_diff(f2, b);
            (f1 - b) + dt + df2b
        };
        
        results.push(travel_time);
        i += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}