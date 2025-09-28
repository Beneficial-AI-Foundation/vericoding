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
fn compute_travel_time(t1: i8, f1: i8, t2: i8, f2: i8, a: i8, b: i8) -> (time: i8)
    requires
        1 <= a <= b,
        1 <= t1, 1 <= f1, 1 <= t2, 1 <= f2,
    ensures
        time as int == min_travel_time(t1 as int, f1 as int, t2 as int, f2 as int, a as int, b as int),
{
    let t1_int = t1 as int;
    let f1_int = f1 as int;
    let t2_int = t2 as int;
    let f2_int = f2 as int;
    let a_int = a as int;
    let b_int = b as int;

    let result = if t1_int == t2_int {
        if f1_int >= f2_int { f1_int - f2_int } else { f2_int - f1_int }
    } else if f1_int >= a_int && f1_int <= b_int {
        let horiz_dist = if t2_int >= t1_int { t2_int - t1_int } else { t1_int - t2_int };
        let vert_dist = if f2_int >= f1_int { f2_int - f1_int } else { f1_int - f2_int };
        horiz_dist + vert_dist
    } else if f1_int < a_int {
        let dist_to_a = a_int - f1_int;
        let horiz_dist = if t2_int >= t1_int { t2_int - t1_int } else { t1_int - t2_int };
        let dist_from_a = if f2_int >= a_int { f2_int - a_int } else { a_int - f2_int };
        dist_to_a + horiz_dist + dist_from_a
    } else {
        let dist_to_b = f1_int - b_int;
        let horiz_dist = if t2_int >= t1_int { t2_int - t1_int } else { t1_int - t2_int };
        let dist_from_b = if f2_int >= b_int { f2_int - b_int } else { b_int - f2_int };
        dist_to_b + horiz_dist + dist_from_b
    };

    proof {
        assert(result == min_travel_time(t1_int, f1_int, t2_int, f2_int, a_int, b_int));
    }

    result as i8
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
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let queries_spec = queries@.map_values(|x: (i8, i8, i8, i8)| (x.0 as int, x.1 as int, x.2 as int, x.3 as int));

    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            queries@.len() == queries_spec.len(),
            valid_building_params(n as int, h as int, a as int, b as int),
            valid_queries(queries_spec, n as int, h as int),
            results.len() == i,
            correct_results(
                queries_spec.subrange(0, i as int),
                results@.map_values(|x: i8| x as int),
                a as int,
                b as int,
            ),
        decreases queries.len() - i
    {
        let query = queries[i];
        let (t1, f1, t2, f2) = query;

        let time = compute_travel_time(t1, f1, t2, f2, a, b);
        results.push(time);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}