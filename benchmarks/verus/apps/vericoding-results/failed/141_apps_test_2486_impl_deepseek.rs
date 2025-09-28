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
proof fn lemma_seq_to_multiset_decreasing_count_helper(sorted: Seq<int>, sorted2: Seq<int>, k: int, temp: int, ans: int, i: int)
    requires
        sorted.len() == sorted2.len(),
        sorted.to_multiset() == sorted2.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < sorted2.len() ==> sorted2[i] >= sorted2[j],
        forall|i: int| 0 <= i < sorted2.len() ==> sorted2[i] >= 1,
        k >= 1,
        0 <= i <= sorted.len(),
        temp >= 0,
        ans >= 0
    ensures
        unnecessary_cards_count_helper(sorted, k, temp, ans, i) == unnecessary_cards_count_helper(sorted2, k, temp, ans, i)
    decreases sorted.len() - i
{
    /* helper modified by LLM (iteration 5): Fixed recursive calls with proper preconditions */
    if i >= sorted.len() {
    } else {
        let x = sorted[i];
        let x2 = sorted2[i];
        
        if temp + x < k {
            assert(temp + x >= 0);
            lemma_seq_to_multiset_decreasing_count_helper(sorted, sorted2, k, temp + x, ans + 1, i + 1);
        } else {
            lemma_seq_to_multiset_decreasing_count_helper(sorted, sorted2, k, 0, 0, i + 1);
        }
    }
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
    /* code modified by LLM (iteration 5): Fixed sorting, arithmetic safety, and verification */
    let mut a_copy = a.clone();
    
    let mut i = 0;
    while i < a_copy.len()
        invariant
            i >= 0 && i <= a_copy.len(),
            forall|x: int| 0 <= x < a_copy.len() ==> a_copy[x] as int >= 1
        decreases a_copy.len() - i
    {
        let mut j = i + 1;
        while j < a_copy.len()
            invariant
                j >= i + 1 && j <= a_copy.len(),
                forall|p: int, q: int| 0 <= p < q <= i ==> a_copy[p] as int >= a_copy[q] as int,
                forall|x: int| 0 <= x < a_copy.len() ==> a_copy[x] as int >= 1
            decreases a_copy.len() - j
        {
            if a_copy[i] < a_copy[j] {
                let temp = a_copy[i];
                a_copy[i] = a_copy[j];
                a_copy[j] = temp;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    let mut temp: i8 = 0;
    let mut ans: i8 = 0;
    let mut i = 0;
    
    while i < a_copy.len()
        invariant
            temp >= 0,
            ans >= 0,
            i >= 0 && i <= a_copy.len(),
            forall|x: int| 0 <= x < a_copy.len() ==> a_copy[x] as int >= 1
        decreases a_copy.len() - i
    {
        let x = a_copy[i];
        if (temp as i16) + (x as i16) < (k as i16) {
            temp = (temp as i16 + x as i16) as i8;
            ans = ans + 1;
        } else {
            temp = 0;
            ans = 0;
        }
        i = i + 1;
    }
    
    proof {
        let sorted_spec = a_copy@.map(|i: int, x: i8| x as int);
        assert forall|i: int, j: int| 0 <= i < j < sorted_spec.len() implies sorted_spec[i] >= sorted_spec[j] by {
            assert(sorted_spec[i] == a_copy[i] as int);
            assert(sorted_spec[j] == a_copy[j] as int);
        };
        assert forall|i: int| 0 <= i < sorted_spec.len() implies sorted_spec[i] >= 1 by {
            assert(sorted_spec[i] == a_copy[i] as int);
        };
        lemma_unnecessary_cards_count_decreasing(a@.map(|i: int, x: i8| x as int), sorted_spec, k as int);
    }
    
    ans
}
// </vc-code>


}

fn main() {}