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
/* helper modified by LLM (iteration 5): fixed lemma proofs and added overflow checking lemmas */
proof fn lemma_min_distance_bounds(cities: Seq<int>, i: int)
    requires
        valid_input(cities),
        0 <= i < cities.len(),
    ensures
        min_distance(cities, i) > 0,
        min_distance(cities, i) <= cities[cities.len()-1] - cities[0],
{
    assert(forall|k: int, l: int| 0 <= k < l < cities.len() ==> cities[k] < cities[l]);
}

proof fn lemma_max_distance_bounds(cities: Seq<int>, i: int)
    requires
        valid_input(cities),
        0 <= i < cities.len(),
    ensures
        max_distance(cities, i) > 0,
        max_distance(cities, i) <= cities[cities.len()-1] - cities[0],
{
    assert(forall|k: int, l: int| 0 <= k < l < cities.len() ==> cities[k] < cities[l]);
}

proof fn lemma_i8_conversion_preserves_order(cities: Vec<i8>)
    requires
        valid_input(cities@.map(|i, v: i8| v as int)),
    ensures
        forall|i: int, j: int| 0 <= i < j < cities.len() ==> cities@[i] as int < cities@[j] as int,
{
    let cities_int = cities@.map(|i, v: i8| v as int);
    assert(forall|i: int, j: int| 0 <= i < j < cities.len() ==> cities_int[i] < cities_int[j]);
    assert(forall|i: int, j: int| 0 <= i < j < cities.len() ==> cities@[i] as int < cities@[j] as int);
}

proof fn lemma_i8_differences_in_bounds(cities: Vec<i8>)
    requires
        valid_input(cities@.map(|i, v: i8| v as int)),
        cities.len() >= 2,
    ensures
        forall|i: int| 0 <= i < cities.len() - 1 ==> 
            (cities@[i+1] as int - cities@[i] as int) <= 127 &&
            (cities@[i+1] as int - cities@[i] as int) >= -128,
        forall|i: int| 0 <= i < cities.len() ==> 
            (cities@[cities.len()-1] as int - cities@[i] as int) <= 127 &&
            (cities@[cities.len()-1] as int - cities@[i] as int) >= -128,
{
}
// </vc-helpers>

// <vc-spec>
fn calculate_distances(cities: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
  requires valid_input(cities@.map(|i, v: i8| v as int))
  ensures valid_output(cities@.map(|i, v: i8| v as int), result.0@.map(|i, v: i8| v as int), result.1@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added overflow checks and fixed arithmetic operations */
    let mut min_distances: Vec<i8> = Vec::new();
    let mut max_distances: Vec<i8> = Vec::new();
    
    proof {
        lemma_i8_conversion_preserves_order(cities);
        lemma_i8_differences_in_bounds(cities);
    }
    
    let mut idx = 0;
    while idx < cities.len()
        invariant
            0 <= idx <= cities.len(),
            min_distances.len() == idx,
            max_distances.len() == idx,
            valid_input(cities@.map(|i, v: i8| v as int)),
            forall|k: int| 0 <= k < idx ==> 
                min_distances@[k] as int == min_distance(cities@.map(|i, v: i8| v as int), k) &&
                max_distances@[k] as int == max_distance(cities@.map(|i, v: i8| v as int), k),
        decreases cities.len() - idx
    {
        let min_dist_int = if idx == 0 {
            cities@[1] as int - cities@[0] as int
        } else if idx == cities.len() - 1 {
            cities@[idx] as int - cities@[idx - 1] as int
        } else {
            let left_dist = cities@[idx] as int - cities@[idx - 1] as int;
            let right_dist = cities@[idx + 1] as int - cities@[idx] as int;
            if left_dist <= right_dist { left_dist } else { right_dist }
        };
        
        let max_dist_int = if idx == 0 {
            cities@[cities.len() - 1] as int - cities@[0] as int
        } else if idx == cities.len() - 1 {
            cities@[idx] as int - cities@[0] as int
        } else {
            let dist_to_first = cities@[idx] as int - cities@[0] as int;
            let dist_to_last = cities@[cities.len() - 1] as int - cities@[idx] as int;
            if dist_to_first >= dist_to_last { dist_to_first } else { dist_to_last }
        };
        
        proof {
            let cities_int = cities@.map(|i, v: i8| v as int);
            lemma_min_distance_bounds(cities_int, idx as int);
            lemma_max_distance_bounds(cities_int, idx as int);
            assert(-128 <= min_dist_int <= 127);
            assert(-128 <= max_dist_int <= 127);
        }
        
        min_distances.push(min_dist_int as i8);
        max_distances.push(max_dist_int as i8);
        
        idx += 1;
    }
    
    (min_distances, max_distances)
}
// </vc-code>


}

fn main() {}