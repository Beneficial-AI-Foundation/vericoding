// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(cities: Seq<int>) -> bool {
  cities.len() >= 2 &&
  forall|i: int, j: int| 0 <= i < j < cities.len() ==> cities[i] < cities[j]
}

spec fn min_distance(cities: Seq<int>, i: int) -> int 
  recommends
    valid_input(cities),
    0 <= i < cities.len()
{
  if i == 0 {
    cities[1] - cities[0]
  } else if i == cities.len() - 1 {
    cities[i] - cities[i-1]
  } else {
    let left_dist = cities[i] - cities[i-1];
    let right_dist = cities[i+1] - cities[i];
    if left_dist <= right_dist { left_dist } else { right_dist }
  }
}

spec fn max_distance(cities: Seq<int>, i: int) -> int 
  recommends
    valid_input(cities),
    0 <= i < cities.len()
{
  if i == 0 {
    cities[cities.len()-1] - cities[0]
  } else if i == cities.len() - 1 {
    cities[i] - cities[0]
  } else {
    let dist_to_first = cities[i] - cities[0];
    let dist_to_last = cities[cities.len()-1] - cities[i];
    if dist_to_first >= dist_to_last { dist_to_first } else { dist_to_last }
  }
}

spec fn valid_output(cities: Seq<int>, min_distances: Seq<int>, max_distances: Seq<int>) -> bool {
  valid_input(cities) &&
  min_distances.len() == cities.len() &&
  max_distances.len() == cities.len() &&
  forall|i: int| 0 <= i < cities.len() ==> 
    min_distances[i] == min_distance(cities, i) &&
    max_distances[i] == max_distance(cities, i) &&
    min_distances[i] > 0 &&
    max_distances[i] > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): positivity of difference when a < b */
proof fn lemma_diff_pos(a: int, b: int)
    requires
        a < b,
    ensures
        b - a > 0,
{
    assert(b - a > 0);
}

/* helper modified by LLM (iteration 4): derive length >= 2 from valid_input */
proof fn lemma_len_ge_2_from_valid_input(cities: Seq<int>)
    requires
        valid_input(cities),
    ensures
        cities.len() >= 2,
{
    assert(cities.len() >= 2);
}

/* helper modified by LLM (iteration 4): min_distance is always positive under valid_input */
proof fn lemma_min_distance_positive(cities: Seq<int>, i: int)
    requires
        valid_input(cities),
        0 <= i < cities.len(),
    ensures
        min_distance(cities, i) > 0,
{
    if i == 0 {
        assert(cities.len() >= 2);
        assert(0 <= 0 < 1 < cities.len());
        assert(cities[0] < cities[1]);
        lemma_diff_pos(cities[0], cities[1]);
        assert(min_distance(cities, i) == cities[1] - cities[0]);
    } else if i == cities.len() - 1 {
        assert(i >= 1);
        assert(0 <= i - 1 < i < cities.len());
        assert(cities[i - 1] < cities[i]);
        lemma_diff_pos(cities[i - 1], cities[i]);
        assert(min_distance(cities, i) == cities[i] - cities[i - 1]);
    } else {
        assert(i >= 1);
        assert(i + 1 < cities.len());
        assert(0 <= i - 1 < i < cities.len());
        assert(0 <= i < i + 1 < cities.len());
        assert(cities[i - 1] < cities[i]);
        assert(cities[i] < cities[i + 1]);
        lemma_diff_pos(cities[i - 1], cities[i]);
        lemma_diff_pos(cities[i], cities[i + 1]);
        let left_dist = cities[i] - cities[i - 1];
        let right_dist = cities[i + 1] - cities[i];
        if left_dist <= right_dist {
            assert(min_distance(cities, i) == left_dist);
        } else {
            assert(min_distance(cities, i) == right_dist);
        }
    }
    assert(min_distance(cities, i) > 0);
}

/* helper modified by LLM (iteration 4): max_distance is always positive under valid_input */
proof fn lemma_max_distance_positive(cities: Seq<int>, i: int)
    requires
        valid_input(cities),
        0 <= i < cities.len(),
    ensures
        max_distance(cities, i) > 0,
{
    let last = cities.len() - 1;
    if i == 0 {
        assert(cities.len() >= 2);
        assert(last < cities.len());
        assert(0 < last);
        assert(0 <= 0 < last < cities.len());
        assert(cities[0] < cities[last]);
        lemma_diff_pos(cities[0], cities[last]);
        assert(max_distance(cities, i) == cities[last] - cities[0]);
    } else if i == last {
        assert(0 <= 0 < i < cities.len());
        assert(cities[0] < cities[i]);
        lemma_diff_pos(cities[0], cities[i]);
        assert(max_distance(cities, i) == cities[i] - cities[0]);
    } else {
        assert(i < last);
        assert(0 <= 0 < i < cities.len());
        assert(0 <= i < last < cities.len());
        assert(cities[0] < cities[i]);
        assert(cities[i] < cities[last]);
        lemma_diff_pos(cities[0], cities[i]);
        lemma_diff_pos(cities[i], cities[last]);
        let dist_to_first = cities[i] - cities[0];
        let dist_to_last = cities[last] - cities[i];
        if dist_to_first >= dist_to_last {
            assert(max_distance(cities, i) == dist_to_first);
        } else {
            assert(max_distance(cities, i) == dist_to_last);
        }
    }
    assert(max_distance(cities, i) > 0);
}
// </vc-helpers>

// <vc-spec>
fn calculate_distances(cities: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
  requires valid_input(cities@.map(|i, v: i8| v as int))
  ensures valid_output(cities@.map(|i, v: i8| v as int), result.0@.map(|i, v: i8| v as int), result.1@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): add length proof, safe indexing, refined invariants, and post-loop positivity proof via lemmas */
{
    let n = cities.len();
    proof {
        lemma_len_ge_2_from_valid_input(cities@.map(|i, v: i8| v as int));
    }
    assert(cities@.len() == n as int);
    assert((cities@.map(|i, v: i8| v as int)).len() == cities@.len());
    assert(n >= 2);

    let ghost ni: int = n as int;
    let mut min_v: Vec<i8> = Vec::new();
    let mut max_v: Vec<i8> = Vec::new();
    let mut ui: usize = 0;
    while ui < n
        invariant
            valid_input(cities@.map(|i, v: i8| v as int)),
            cities@.len() == n as int,
            (cities@.map(|i, v: i8| v as int)).len() == cities@.len(),
            0 <= ui as int <= ni,
            min_v.len() == ui,
            max_v.len() == ui,
            forall|j: int| 0 <= j < ui as int ==> (min_v@[j] as int) == min_distance(cities@.map(|i, v: i8| v as int), j),
            forall|j: int| 0 <= j < ui as int ==> (max_v@[j] as int) == max_distance(cities@.map(|i, v: i8| v as int), j),
        decreases ni - ui as int
    {
        if ui == 0 {
            assert(n >= 2);
            assert(0 < n);
            assert(1 < n);
            let dmin_i32: i32 = (cities[1] as i32) - (cities[0] as i32);
            let last_idx: usize = n - 1;
            assert(last_idx < n);
            let dmax_i32: i32 = (cities[last_idx] as i32) - (cities[0] as i32);
            min_v.push(#[verifier::truncate] (dmin_i32 as i8));
            max_v.push(#[verifier::truncate] (dmax_i32 as i8));
        } else if ui == n - 1 {
            assert(ui < n);
            assert(ui >= 1);
            assert(ui - 1 < ui);
            assert(ui - 1 < n);
            let dmin_i32: i32 = (cities[ui] as i32) - (cities[ui - 1] as i32);
            let dmax_i32: i32 = (cities[ui] as i32) - (cities[0] as i32);
            min_v.push(#[verifier::truncate] (dmin_i32 as i8));
            max_v.push(#[verifier::truncate] (dmax_i32 as i8));
        } else {
            assert(ui > 0);
            assert(ui + 1 < n);
            assert(ui - 1 < ui);
            assert(ui - 1 < n);
            let dleft_i32: i32 = (cities[ui] as i32) - (cities[ui - 1] as i32);
            let dright_i32: i32 = (cities[ui + 1] as i32) - (cities[ui] as i32);
            let dmin_i32: i32 = if dleft_i32 <= dright_i32 { dleft_i32 } else { dright_i32 };
            let d1_i32: i32 = (cities[ui] as i32) - (cities[0] as i32);
            let last_idx: usize = n - 1;
            assert(last_idx < n);
            let d2_i32: i32 = (cities[last_idx] as i32) - (cities[ui] as i32);
            let dmax_i32: i32 = if d1_i32 >= d2_i32 { d1_i32 } else { d2_i32 };
            min_v.push(#[verifier::truncate] (dmin_i32 as i8));
            max_v.push(#[verifier::truncate] (dmax_i32 as i8));
        }
        ui = ui + 1;
    }

    proof {
        assert(ui == n);
        assert(ui as int == ni);
        assert forall|j: int| 0 <= j < ni ==> (min_v@[j] as int) > 0 by {
            let j = j;
            assert(0 <= j < ni);
            assert(0 <= j < ui as int);
            assert((min_v@[j] as int) == min_distance(cities@.map(|i, v: i8| v as int), j));
            lemma_min_distance_positive(cities@.map(|i, v: i8| v as int), j);
        };
        assert forall|j: int| 0 <= j < ni ==> (max_v@[j] as int) > 0 by {
            let j = j;
            assert(0 <= j < ni);
            assert(0 <= j < ui as int);
            assert((max_v@[j] as int) == max_distance(cities@.map(|i, v: i8| v as int), j));
            lemma_max_distance_positive(cities@.map(|i, v: i8| v as int), j);
        };
    }

    (min_v, max_v)
}
// </vc-code>


}

fn main() {}