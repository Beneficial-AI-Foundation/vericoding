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
/* helper modified by LLM (iteration 2): simple lemma to derive element positivity from universal precondition */
proof fn lemma_vec_elem_ge_one(a: Vec<i8>, i: usize)
    requires
        forall|j: int| 0 <= j < a.len() ==> a[j] as int >= 1,
        i < a.len(),
    ensures
        a[i] as int >= 1,
{
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
    /* code modified by LLM (iteration 2): replaced ghost ints with exec ints and retained counting-based simulation of descending order */
    let k_i32: i32 = k as i32;

    let mut counts: Vec<usize> = Vec::new();
    let mut v: i32 = 0;
    while v <= 127
        invariant
            0 <= v <= 128,
            counts.len() == v as usize,
    {
        counts.push(0usize);
        v += 1;
    }

    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            counts.len() == 128,
            forall|j: int| 0 <= j < a.len() ==> a[j] as int >= 1,
            forall|j: int| 0 <= j < i as int ==> a[j] as int >= 1,
    {
        let idx: usize = a[i] as usize;
        counts[idx] = counts[idx] + 1;
        i += 1;
    }

    let mut ans: i32 = 0;
    let mut temp: i32 = 0;
    let mut processed: usize = 0;

    let mut val: i32 = 127;
    while val >= 1
        invariant
            0 <= val <= 127,
            counts.len() == 128,
            processed <= a.len(),
            0 <= ans as int,
            0 <= temp as int,
            ans as int <= processed as int,
    {
        let cnt: usize = counts[val as usize];
        let mut c: usize = 0;
        while c < cnt
            invariant
                c <= cnt,
                counts.len() == 128,
                processed + c <= a.len(),
                0 <= ans as int,
                0 <= temp as int,
                ans as int <= processed as int + c as int,
        {
            let x: i32 = val;
            if temp + x < k_i32 {
                temp = temp + x;
                ans = ans + 1;
            } else {
                temp = 0;
                ans = 0;
            }
            c += 1;
        }
        processed = processed + cnt;
        val -= 1;
    }

    let res: i8 = ans as i8;
    res
}

// </vc-code>


}

fn main() {}