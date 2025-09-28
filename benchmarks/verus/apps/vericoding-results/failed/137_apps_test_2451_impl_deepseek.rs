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
/* helper modified by LLM (iteration 5): Fix syntax errors and improve casting */
fn min_travel_time_impl(t1: i8, f1: i8, t2: i8, f2: i8, a: i8, b: i8) -> (result: i8)
    requires
        valid_query((t1 as int, f1 as int, t2 as int, f2 as int), 127, 127),
        valid_building_params(127, 127, a as int, b as int),
    ensures
        result as int == min_travel_time(t1 as int, f1 as int, t2 as int, f2 as int, a as int, b as int),
{
    if t1 == t2 {
        if f1 >= f2 { (f1 - f2) as i8 } else { (f2 - f1) as i8 }
    } else if f1 >= a && f1 <= b {
        let horizontal = if t2 >= t1 { (t2 - t1) as i16 } else { (t1 - t2) as i16 };
        let vertical = if f2 >= f1 { (f2 - f1) as i16 } else { (f1 - f2) as i16 };
        (horizontal + vertical) as i8
    } else if f1 < a {
        let to_a = (a - f1) as i16;
        let horizontal = if t2 >= t1 { (t2 - t1) as i16 } else { (t1 - t2) as i16 };
        let from_a = if f2 >= a { (f2 - a) as i16 } else { (a - f2) as i16 };
        (to_a + horizontal + from_a) as i8
    } else {
        let to_b = (f1 - b) as i16;
        let horizontal = if t2 >= t1 { (t2 - t1) as i16 } else { (t1 - t2) as i16 };
        let from_b = if f2 >= b { (f2 - b) as i16 } else { (b - f2) as i16 };
        (to_b + horizontal + from_b) as i8
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
/* code modified by LLM (iteration 5): Fix while loop indexing with proper cast */
{
    let mut results = Vec::new();
    
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] results@[j] as int == min_travel_time(
                queries@[j].0 as int, queries@[j].1 as int, queries@[j].2 as int, queries@[j].3 as int, 
                a as int, b as int
            ),
        decreases queries.len() - i,
    {
        let query = queries.index(i);
        let (t1, f1, t2, f2) = query;
        let result = min_travel_time_impl(t1, f1, t2, f2, a, b);
        results.push(result);
        i += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}