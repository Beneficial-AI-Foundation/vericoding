// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn unnecessary_cards_count(sorted: Seq<int>, k: int) -> int
  recommends
    forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] >= sorted[j],
    forall|i: int| 0 <= i < sorted.len() ==> sorted[i] >= 1,
    k >= 1
{
  if sorted.len() == 0 {
    0
  } else {
    unnecessary_cards_count_helper(sorted, k, 0, 0, 0)
  }
}

spec fn unnecessary_cards_count_helper(sorted: Seq<int>, k: int, temp: int, ans: int, i: int) -> int
  recommends
    forall|x: int, y: int| 0 <= x < y < sorted.len() ==> sorted[x] >= sorted[y],
    forall|x: int| 0 <= x < sorted.len() ==> sorted[x] >= 1,
    k >= 1,
    0 <= i <= sorted.len(),
    temp >= 0,
    ans >= 0
  decreases sorted.len() - i
{
  if i >= sorted.len() {
    ans
  } else {
    let x = sorted[i];
    if temp + x < k {
      unnecessary_cards_count_helper(sorted, k, temp + x, ans + 1, i + 1)
    } else {
      unnecessary_cards_count_helper(sorted, k, 0, 0, i + 1)
    }
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to fix compilation error */
fn sort_preserves_elements<T>(vec: Vec<T>, sorted_vec: Vec<T>)
    requires
        sorted_vec@.to_multiset() == vec@.to_multiset(),
    ensures
        sorted_vec@.len() == vec@.len(),
{
}

fn manual_sort(vec: Vec<i8>) -> (sorted: Vec<i8>)
    requires
        vec.len() > 0,
        forall|i: int| 0 <= i < vec.len() ==> vec[i] as int >= 1,
    ensures
        sorted@.len() == vec@.len(),
        sorted@.to_multiset() == vec@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] as int >= sorted[j] as int,
        forall|i: int| 0 <= i < sorted.len() ==> sorted[i] as int >= 1,
{
    let mut sorted = vec;
    let mut i = 0;
    while i < sorted.len()
        invariant
            0 <= i <= sorted.len(),
            sorted@.len() == vec@.len(),
            sorted@.to_multiset() == vec@.to_multiset(),
            forall|k: int| 0 <= k < sorted.len() ==> sorted[k] as int >= 1,
        decreases sorted.len() - i
    {
        let mut j = i + 1;
        while j < sorted.len()
            invariant
                i < j <= sorted.len(),
                sorted@.len() == vec@.len(),
                sorted@.to_multiset() == vec@.to_multiset(),
                forall|k: int| 0 <= k < sorted.len() ==> sorted[k] as int >= 1,
            decreases sorted.len() - j
        {
            if sorted[i] < sorted[j] {
                let temp = sorted[i];
                sorted.set(i, sorted[j]);
                sorted.set(j, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    sorted
}

fn count_unnecessary_cards(sorted: &Vec<i8>, k: i8) -> (result: i8)
    requires
        sorted.len() > 0,
        forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] as int >= sorted[j] as int,
        forall|i: int| 0 <= i < sorted.len() ==> sorted[i] as int >= 1,
        k >= 1,
    ensures
        result >= 0,
        result as int == unnecessary_cards_count(sorted@.map(|i: int, x: i8| x as int), k as int),
{
    let mut temp: i8 = 0;
    let mut ans: i8 = 0;
    let mut i: usize = 0;
    
    while i < sorted.len()
        invariant
            0 <= i <= sorted.len(),
            temp >= 0,
            ans >= 0,
        decreases sorted.len() - i
    {
        let x = sorted[i];
        if temp + x < k {
            temp = temp + x;
            ans = ans + 1;
        } else {
            temp = 0;
            ans = 0;
        }
        i = i + 1;
    }
    ans
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: i8)
  requires
    n >= 1,
    k >= 1,
    a.len() == n as usize,
    forall|i: int| 0 <= i < a.len() ==> a[i] as int >= 1
  ensures
    result >= 0,
    result as int <= n as int,
    exists|sorted: Seq<int>|
      sorted.len() == a@.len() &&
      sorted.to_multiset() == a@.map(|i: int, x: i8| x as int).to_multiset() &&
      (forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] >= sorted[j]) &&
      (forall|i: int| 0 <= i < sorted.len() ==> sorted[i] >= 1) &&
      result as int == unnecessary_cards_count(sorted, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed for code section */
    let mut sorted_a = manual_sort(a);
    
    if sorted_a.len() == 0 {
        return 0;
    }
    
    let result = count_unnecessary_cards(&sorted_a, k);
    
    proof {
        let sorted_seq = sorted_a@.map(|i: int, x: i8| x as int);
        assert(sorted_seq.len() == a@.len());
        assert(sorted_seq.to_multiset() == a@.map(|i: int, x: i8| x as int).to_multiset());
        assert(forall|i: int, j: int| 0 <= i < j < sorted_seq.len() ==> sorted_seq[i] >= sorted_seq[j]);
        assert(forall|i: int| 0 <= i < sorted_seq.len() ==> sorted_seq[i] >= 1);
    }
    
    result
}
// </vc-code>


}

fn main() {}