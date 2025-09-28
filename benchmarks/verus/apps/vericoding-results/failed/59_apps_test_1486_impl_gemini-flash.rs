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
/* helper modified by LLM (iteration 5): removed unnecessary code to simplify */
// </vc-helpers>

// <vc-spec>
fn calculate_distances(cities: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
  requires valid_input(cities@.map(|i, v: i8| v as int))
  ensures valid_output(cities@.map(|i, v: i8| v as int), result.0@.map(|i, v: i8| v as int), result.1@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added explicit type casting */
{
    let ghost_cities_seq = cities@.map(|_i, v: i8| v as int);

    let mut min_dists: Vec<i8> = Vec::new();
    let mut max_dists: Vec<i8> = Vec::new();

    let len = cities.len();
    if len == 0 {
        return (min_dists, max_dists);
    }

    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i && i <= len,
            min_dists.len() == i,
            max_dists.len() == i,
            forall|j: int| 0 <= j < i ==> 
                min_dists@[j] as int == min_distance(ghost_cities_seq, j) &&
                max_dists@[j] as int == max_distance(ghost_cities_seq, j),
            valid_input(ghost_cities_seq),
    {
        let mut current_min_dist: i8;
        let mut current_max_dist: i8;

        if i == 0 {
            current_min_dist = cities[1] - cities[0];
            current_max_dist = cities[len - 1] - cities[0];
        } else if i == len - 1 {
            current_min_dist = cities[i] - cities[i - 1];
            current_max_dist = cities[i] - cities[0];
        } else {
            let left_dist = cities[i] - cities[i - 1];
            let right_dist = cities[i + 1] - cities[i];
            current_min_dist = if left_dist <= right_dist { left_dist } else { right_dist };

            let dist_to_first = cities[i] - cities[0];
            let dist_to_last = cities[len - 1] - cities[i];
            current_max_dist = if dist_to_first >= dist_to_last { dist_to_first } else { dist_to_last };
        }

        min_dists.push(current_min_dist);
        max_dists.push(current_max_dist);

        i = i + 1;
    }
    
    (min_dists, max_dists)
}
// </vc-code>


}

fn main() {}