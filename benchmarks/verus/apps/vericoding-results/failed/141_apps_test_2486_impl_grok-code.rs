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
fn sort_desc(a: &Vec<i8>) -> (result: Vec<i8>)
    requires
        forall|i: int| 0 <= i < a.len() ==> a[i] as int >= 1
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int >= result[j] as int,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int >= 1,
        result@.map(|x: i8| x as int).to_multiset() == a@.map(|x: i8| x as int).to_multiset()
{
    let mut v = a.clone();
    let n = v.len();
    for i in 0..n {
        for j in 0..(n - i - 1) {
            if v[j] < v[j + 1] {
                let temp = v[j];
                v.set(j, v[j + 1]);
                v.set(j + 1, temp);
            }
        }
    }
    v
}

/* helper modified by LLM (iteration 5): fixed Tracked syntax and variable updates for ghost values in exec function */
fn unnecessary_cards_count_exec(sorted: &Vec<i8>, k: i8) -> (result: i8)
    requires
        k >= 1,
        forall|i: int| 0 <= i < sorted.len() ==> sorted[i] as int >= 1,
        forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] as int >= sorted[j] as int
    ensures
        result as int == unnecessary_cards_count(sorted@.map(|x: i8| x as int), k as int),
        result >= 0,
        result as int <= sorted.len()
{
    let mut ans: i8 = 0;
    let mut temp: Tracked<int> = Tracked(0);
    let mut i: Tracked<int> = Tracked(0);
    while *i < sorted.len() as int
        invariant
            0 <= *i,
            *i <= sorted.len() as int,
            *temp >= 0,
            ans >= 0,
            ans as int <= *i as int,
            ans as int + unnecessary_cards_count_helper(sorted@.map(|x: i8| x as int), k as int, *temp, ans as int, *i) == unnecessary_cards_count(sorted@.map(|x: i8| x as int), k as int)
        decreases (sorted.len() as int - *i)
    {
        let x = sorted[*i as usize];
        if *temp + (x as int) < k as int {
            ans = ans + 1;
            *temp = *temp + (x as int);
        } else {
            ans = 0;
            *temp = 0;
        }
        *i = *i + 1;
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
/* code modified by LLM (iteration 5): implemented sorting and counting logic */
{
    let sorted = sort_desc(&a);
    let count = unnecessary_cards_count_exec(&sorted, k);
    count
}
// </vc-code>


}

fn main() {}