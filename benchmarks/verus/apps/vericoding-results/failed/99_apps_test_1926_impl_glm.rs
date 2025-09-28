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
/* helper modified by LLM (iteration 5): fixed parent index calculation to work with Range instead of RangeInclusive */
fn parent_index(i: i32, k: i32) -> (result: i32)
    requires i >= 2 && k >= 1
    ensures result >= 1
{
    (i + k - 2) / k
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: Vec<i8>)
  requires valid_input(n as int, a@.map(|_i, x| x as int))
  ensures valid_output(result@.map(|_i, x| x as int), n as int, a@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced RangeInclusive with Range to fix compilation error */
    let mut result = Vec::new();
    for k in 1..n {
        let mut count: i8 = 0;
        for i in 2i32..(n as i32 + 1) {
            let parent_idx = parent_index(i, k as i32);
            assert(parent_idx >= 1 && parent_idx <= n as i32);
            assert(i >= 1 && i <= n as i32);
            if a[(i - 1) as usize] < a[(parent_idx - 1) as usize] {
                count += 1;
            }
        }
        result.push(count);
    }
    result
}
// </vc-code>


}

fn main() {}