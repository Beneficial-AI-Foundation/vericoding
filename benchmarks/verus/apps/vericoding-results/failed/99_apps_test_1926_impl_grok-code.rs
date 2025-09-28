// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
  n >= 2 && a.len() == n
}

spec fn count_violations_for_k(a: Seq<int>, n: int, k: int) -> int {
  let violations = Set::new(|i: int| 2 <= i <= n && {
    let parent_idx = (i + k - 2) / k;
    parent_idx >= 1 && a[i-1] < a[parent_idx-1]
  });
  violations.len() as int
}

spec fn valid_output(result: Seq<int>, n: int, a: Seq<int>) -> bool {
  result.len() == n - 1 &&
  (forall|k: int| 1 <= k <= n - 1 ==> #[trigger] result[k-1] >= 0) &&
  (forall|k: int| 1 <= k <= n - 1 ==> #[trigger] result[k-1] == count_violations_for_k(a, n, k))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed loop range to use usize instead of i8 to satisfy ForLoopGhostIteratorNew trait, simplified parent_idx calculation */
fn exec_count_violations(a: &Vec<i8>, k: i8) -> (result: i8)
    requires
        1 <= k as int <= (a.len() as int - 1),
        2 <= a.len() as int,
    ensures
        result as int == count_violations_for_k(a@.map(|_, x| x as int), a.len() as int, k as int),
{
    let mut count: i8 = 0;
    for i in 2..=a.len() {
        let parent_idx = (i + (k as usize) - 2) / (k as usize);
        if parent_idx >= 1 && a[i - 1] < a[parent_idx - 1] {
            count += 1;
        }
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: Vec<i8>)
  requires valid_input(n as int, a@.map(|_i, x| x as int))
  ensures valid_output(result@.map(|_i, x| x as int), n as int, a@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): maintained loop for violations per k */
{
    let mut result = Vec::new();
    for kk in 1..(n as usize) {
        let k = kk as i8;
        let count = exec_count_violations(&a, k);
        result.push(count);
    }
    result
}
// </vc-code>


}

fn main() {}