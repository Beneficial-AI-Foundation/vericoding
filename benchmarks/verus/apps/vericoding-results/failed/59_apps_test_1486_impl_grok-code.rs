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
/* helper modified by LLM (iteration 4): added min_i8 and max_i8 functions for i8 arithmetic */
fn min_i8(a: i8, b: i8) -> i8 { if a <= b { a } else { b } }
fn max_i8(a: i8, b: i8) -> i8 { if a >= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn calculate_distances(cities: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
  requires valid_input(cities@.map(|i, v: i8| v as int))
  ensures valid_output(cities@.map(|i, v: i8| v as int), result.0@.map(|i, v: i8| v as int), result.1@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type mismatch by casting i to int in proof assertions */
{
    let cities_seq = cities@;
    let n = cities.len();
    let mut min_distances = Vec::new();
    let mut max_distances = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            min_distances.len() == i,
            max_distances.len() == i,
            forall|k: int| 0 <= k < i ==> 
                min_distances@[k] as int == min_distance(cities_seq.map(|i, v| v as int), k) &&
                max_distances@[k] as int == max_distance(cities_seq.map(|i, v| v as int), k)
        decreases n - i
    {
        let min_d_i8 = if i == 0 {
            cities[1] - cities[0]
        } else if i == n - 1 {
            cities[i] - cities[i-1]
        } else {
            let left = cities[i] - cities[i-1];
            let right = cities[i+1] - cities[i];
            min_i8(left, right)
        };
        proof { assert(min_d_i8 as int == min_distance(cities_seq.map(|i, v| v as int), i as int)); }
        min_distances.push(min_d_i8);
        let max_d_i8 = if i == 0 {
            cities[n-1] - cities[i]
        } else if i == n - 1 {
            cities[i] - cities[0]
        } else {
            let to_first = cities[i] - cities[0];
            let to_last = cities[n-1] - cities[i];
            max_i8(to_first, to_last)
        };
        proof { assert(max_d_i8 as int == max_distance(cities_seq.map(|i, v| v as int), i as int)); }
        max_distances.push(max_d_i8);
        i += 1;
    }
    (min_distances, max_distances)
}
// </vc-code>


}

fn main() {}