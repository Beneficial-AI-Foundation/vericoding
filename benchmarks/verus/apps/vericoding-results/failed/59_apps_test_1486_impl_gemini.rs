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

// </vc-helpers>

// <vc-spec>
fn calculate_distances(cities: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
  requires valid_input(cities@.map(|i, v: i8| v as int))
  ensures valid_output(cities@.map(|i, v: i8| v as int), result.0@.map(|i, v: i8| v as int), result.1@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [Fixed compilation error in map closure.] */
    let n = cities.len();
    
    let mut min_distances: Vec<i8> = Vec::new();
    let mut max_distances: Vec<i8> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            cities.len() == n,
            valid_input(cities@.map(|idx, v: i8| v as int)),
            min_distances.len() == i,
            max_distances.len() == i,
            forall|j: int| 0 <= j < i ==> 
                (min_distances@[j] as int) == min_distance(cities@.map(|idx, v: i8| v as int), j),
            forall|j: int| 0 <= j < i ==> 
                (max_distances@[j] as int) == max_distance(cities@.map(|idx, v: i8| v as int), j)
        decreases n - i
    {
        let min_dist_val = if i == 0 {
            (cities[1] as i32) - (cities[0] as i32)
        } else if i == n - 1 {
            (cities[i] as i32) - (cities[i-1] as i32)
        } else {
            let left_dist = (cities[i] as i32) - (cities[i-1] as i32);
            let right_dist = (cities[i+1] as i32) - (cities[i] as i32);
            if left_dist <= right_dist { left_dist } else { right_dist }
        };

        let max_dist_val = {
            let dist_to_first = (cities[i] as i32) - (cities[0] as i32);
            let dist_to_last = (cities[n-1] as i32) - (cities[i] as i32);
            if dist_to_first >= dist_to_last { dist_to_first } else { dist_to_last }
        };

        let min_d = min_dist_val as i8;
        let max_d = max_dist_val as i8;

        min_distances.push(min_d);
        max_distances.push(max_d);
        
        i = i + 1;
    }

    (min_distances, max_distances)
}
// </vc-code>


}

fn main() {}