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
/* helper modified by LLM (iteration 5): Fixed lemma assertions and proof structure */
proof fn lemma_min_distance_symmetric(cities: Seq<int>, i: int, j: int)
    requires
        valid_input(cities),
        0 <= i < cities.len(),
        0 <= j < cities.len(),
{
    // This lemma is not generally true for different i,j
    // Keep empty - no symmetric property exists
}

proof fn lemma_max_distance_monotonic(cities: Seq<int>, i: int, j: int)
    requires
        valid_input(cities),
        0 <= i < j < cities.len(),
    ensures
        max_distance(cities, i) <= max_distance(cities, j)
{
    assert(max_distance(cities, i) == cities[cities.len()-1] - cities[i]);
    assert(max_distance(cities, j) == cities[cities.len()-1] - cities[j]);
    assert(cities[i] <= cities[j]);
}

proof fn lemma_distance_bounds(cities: Seq<int>, i: int)
    requires
        valid_input(cities),
        0 <= i < cities.len(),
    ensures
        min_distance(cities, i) <= max_distance(cities, i)
{
    if i == 0 {
        assert(min_distance(cities, 0) == cities[1] - cities[0]);
        assert(max_distance(cities, 0) == cities[cities.len()-1] - cities[0]);
        assert(cities[1] <= cities[cities.len()-1]);
    } else if i == cities.len() - 1 {
        assert(min_distance(cities, i) == cities[i] - cities[i-1]);
        assert(max_distance(cities, i) == cities[i] - cities[0]);
        assert(cities[i-1] <= cities[i]);
    } else {
        let left_dist = cities[i] - cities[i-1];
        let right_dist = cities[i+1] - cities[i];
        let min_dist = if left_dist <= right_dist { left_dist } else { right_dist };
        
        let dist_to_first = cities[i] - cities[0];
        let dist_to_last = cities[cities.len()-1] - cities[i];
        let max_dist = if dist_to_first >= dist_to_last { dist_to_first } else { dist_to_last };
        
        assert(left_dist <= dist_to_first || right_dist <= dist_to_first);
        assert(left_dist <= dist_to_last || right_dist <= dist_to_last);
    }
}

proof fn lemma_edge_cases_valid(cities: Seq<int>)
    requires
        valid_input(cities),
    ensures
        min_distance(cities, 0) > 0,
        min_distance(cities, cities.len() - 1) > 0,
        max_distance(cities, 0) > 0,
        max_distance(cities, cities.len() - 1) > 0
{
    assert(cities[0] < cities[1]);
    assert(cities[cities.len()-2] < cities[cities.len()-1]);
    assert(cities[0] < cities[cities.len()-1]);
}
// </vc-helpers>

// <vc-spec>
fn calculate_distances(cities: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
  requires valid_input(cities@.map(|i, v: i8| v as int))
  ensures valid_output(cities@.map(|i, v: i8| v as int), result.0@.map(|i, v: i8| v as int), result.1@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed sequence access syntax */
{
    let n = cities.len();
    assert(n >= 2) by {
        let cities_seq = cities@.map(|i, v: i8| v as int);
        assert(valid_input(cities_seq));
    };
    
    let mut min_dists = Vec::new();
    let mut max_dists = Vec::new();
    
    for i in 0..n {
        invariant
            min_dists@.len() == i,
            max_dists@.len() == i,
            forall|k: int| 0 <= k < i ==> 
                min_dists@[k] as int == min_distance(cities@.map(|i,v| v as int), k) &&
                max_dists@[k] as int == max_distance(cities@.map(|i,v| v as int), k);
        
        if i == 0 {
            assert(1 < n);
            let min_dist = cities[1] - cities[0];
            let max_dist = cities[n-1] - cities[0];
            min_dists.push(min_dist);
            max_dists.push(max_dist);
        } else if i == n - 1 {
            assert(i-1 >= 0);
            let min_dist = cities[i] - cities[i-1];
            let max_dist = cities[i] - cities[0];
            min_dists.push(min_dist);
            max_dists.push(max_dist);
        } else {
            assert(i-1 >= 0 && i+1 < n);
            let left_dist = cities[i] - cities[i-1];
            let right_dist = cities[i+1] - cities[i];
            let min_dist = if left_dist <= right_dist { left_dist } else { right_dist };
            
            let dist_to_first = cities[i] - cities[0];
            let dist_to_last = cities[n-1] - cities[i];
            let max_dist = if dist_to_first >= dist_to_last { dist_to_first } else { dist_to_last };
            
            min_dists.push(min_dist);
            max_dists.push(max_dist);
        }
        
        proof {
            lemma_distance_bounds(cities@.map(|i,v| v as int), i);
        }
    }
    
    (min_dists, max_dists)
}
// </vc-code>


}

fn main() {}