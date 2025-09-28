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
/* helper modified by LLM (iteration 5): ensure min/max distances positive with int index */
spec fn lemma_distance_positive(cities: Seq<int>, i: int)
    requires
        valid_input(cities),
        0 <= i < cities.len(),
    ensures
        min_distance(cities, i) > 0,
        max_distance(cities, i) > 0,
{
    if i == 0 {
        let dmin = cities[1] - cities[0];
        assert(cities[0] < cities[1]);
        assert(dmin > 0);
        assert(min_distance(cities, 0) == dmin);

        let dmax = cities[cities.len() - 1] - cities[0];
        assert(dmax > 0);
        assert(max_distance(cities, 0) == dmax);
    } else if i == cities.len() - 1 {
        let dmin = cities[i] - cities[i - 1];
        assert(dmin > 0);
        assert(min_distance(cities, i) == dmin);

        let dmax = cities[i] - cities[0];
        assert(dmax > 0);
        assert(max_distance(cities, i) == dmax);
    } else {
        let left = cities[i] - cities[i - 1];
        let right = cities[i + 1] - cities[i];
        assert(left > 0);
        assert(right > 0);
        let md = if left <= right { left } else { right };
        assert(min_distance(cities, i) == md);
        assert(min_distance(cities, i) > 0);

        let to_first = cities[i] - cities[0];
        let to_last = cities[cities.len() - 1] - cities[i];
        assert(to_first > 0);
        assert(to_last > 0);
        let M = if to_first >= to_last { to_first } else { to_last };
        assert(max_distance(cities, i) == M);
        assert(max_distance(cities, i) > 0);
    }
}

// </vc-helpers>

// <vc-spec>
fn calculate_distances(cities: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
  requires valid_input(cities@.map(|i, v: i8| v as int))
  ensures valid_output(cities@.map(|i, v: i8| v as int), result.0@.map(|i, v: i8| v as int), result.1@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute min/max distances with proofs and proper index casts */
  let n = cities.len();
  let mut mins: Vec<i8> = Vec::new();
  let mut maxs: Vec<i8> = Vec::new();
  let mut i: usize = 0;
  while i < n
      invariant
          i <= n,
          mins.len() == i,
          maxs.len() == i,
          forall|j: int| 0 <= j < i as int ==> (mins@)[j as nat] as int == min_distance(cities@.map(|_, v: i8| v as int), j) && (maxs@)[j as nat] as int == max_distance(cities@.map(|_, v: i8| v as int), j),
      decreases n - i
  {
      let min_d_i8: i8;
      let max_d_i8: i8;
      if i == 0 {
          min_d_i8 = cities[1usize] - cities[0usize];
          max_d_i8 = cities[n - 1usize] - cities[0usize];
      } else if i + 1 == n {
          min_d_i8 = cities[i] - cities[i - 1];
          max_d_i8 = cities[i] - cities[0usize];
      } else {
          let left: i8 = cities[i] - cities[i - 1];
          let right: i8 = cities[i + 1] - cities[i];
          if left <= right {
              min_d_i8 = left;
          } else {
              min_d_i8 = right;
          }

          let to_first: i8 = cities[i] - cities[0usize];
          let to_last: i8 = cities[n - 1usize] - cities[i];
          if to_first >= to_last {
              max_d_i8 = to_first;
          } else {
              max_d_i8 = to_last;
          }
      }

      proof {
          let idx: int = i as int;
          let min_d_int: int = (min_d_i8) as int;
          let max_d_int: int = (max_d_i8) as int;
          assert(min_d_int == min_distance(cities@.map(|_, v: i8| v as int), idx));
          assert(max_d_int == max_distance(cities@.map(|_, v: i8| v as int), idx));
      }

      mins.push(min_d_i8);
      maxs.push(max_d_i8);
      i += 1;
  }
  (mins, maxs)
}

// </vc-code>


}

fn main() {}