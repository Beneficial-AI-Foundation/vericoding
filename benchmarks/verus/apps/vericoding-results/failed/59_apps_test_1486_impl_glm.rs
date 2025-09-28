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
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn calculate_distances(cities: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
  requires valid_input(cities@.map(|i, v: i8| v as int))
  ensures valid_output(cities@.map(|i, v: i8| v as int), result.0@.map(|i, v: i8| v as int), result.1@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type mismatches by casting indices to int */
{
    let n = cities.len();
    let ghost cities_seq = cities@.map(|i, v: i8| v as int);

    let mut min_distances: Vec<i8> = Vec::new();
    let mut max_distances: Vec<i8> = Vec::new();

    for i in 0..n
        invariant
            min_distances.len() == i,
            max_distances.len() == i,
            forall|j: int| 0 <= j < i ==> 
                min_distances@[j] as int == min_distance(cities_seq, j) &&
                max_distances@[j] as int == max_distance(cities_seq, j) &&
                min_distances@[j] as int > 0 &&
                max_distances@[j] as int > 0,
        decreases n - i
    {
        let min_dist: i8;
        let max_dist: i8;

        if i == 0 {
            min_dist = cities[1] - cities[0];
            max_dist = cities[n-1] - cities[0];
        } else if i == n-1 {
            min_dist = cities[i] - cities[i-1];
            max_dist = cities[i] - cities[0];
        } else {
            let left_val = cities[i] - cities[i-1];
            let right_val = cities[i+1] - cities[i];
            min_dist = if left_val <= right_val { left_val } else { right_val };

            let to_first_val = cities[i] - cities[0];
            let to_last_val = cities[n-1] - cities[i];
            max_dist = if to_first_val >= to_last_val { to_first_val } else { to_last_val };
        }

        min_distances.push(min_dist);
        max_distances.push(max_dist);

        proof {
            let min_dist_spec = min_distance(cities_seq, i as int);
            let max_dist_spec = max_distance(cities_seq, i as int);

            if i == 0 {
                assert(min_dist as int == cities_seq[1] - cities_seq[0]);
                assert(min_dist_spec == cities_seq[1] - cities_seq[0]);
                assert(min_dist as int == min_dist_spec);
            } else if i == n-1 {
                assert(min_dist as int == cities_seq[i as int] - cities_seq[(i-1) as int]);
                assert(min_dist_spec == cities_seq[i as int] - cities_seq[(i-1) as int]);
                assert(min_dist as int == min_dist_spec);
            } else {
                let left_int = cities_seq[i as int] - cities_seq[(i-1) as int];
                let right_int = cities_seq[(i+1) as int] - cities_seq[i as int];
                if cities[i] - cities[i-1] <= cities[i+1] - cities[i] {
                    assert(min_dist as int == left_int);
                } else {
                    assert(min_dist as int == right_int);
                }
                if left_int <= right_int {
                    assert(min_dist_spec == left_int);
                } else {
                    assert(min_dist_spec == right_int);
                }
                assert(min_dist as int == min_dist_spec);
            }

            if i == 0 {
                assert(max_dist as int == cities_seq[(n-1) as int] - cities_seq[0]);
                assert(max_dist_spec == cities_seq[(n-1) as int] - cities_seq[0]);
                assert(max_dist as int == max_dist_spec);
            } else if i == n-1 {
                assert(max_dist as int == cities_seq[i as int] - cities_seq[0]);
                assert(max_dist_spec == cities_seq[i as int] - cities_seq[0]);
                assert(max_dist as int == max_dist_spec);
            } else {
                let to_first_int = cities_seq[i as int] - cities_seq[0];
                let to_last_int = cities_seq[(n-1) as int] - cities_seq[i as int];
                if cities[i] - cities[0] >= cities[n-1] - cities[i] {
                    assert(max_dist as int == to_first_int);
                } else {
                    assert(max_dist as int == to_last_int);
                }
                if to_first_int >= to_last_int {
                    assert(max_dist_spec == to_first_int);
                } else {
                    assert(max_dist_spec == to_last_int);
                }
                assert(max_dist as int == max_dist_spec);
            }

            assert(min_dist > 0);
            assert(max_dist > 0);
        }
    }

    (min_distances, max_distances)
}
// </vc-code>


}

fn main() {}