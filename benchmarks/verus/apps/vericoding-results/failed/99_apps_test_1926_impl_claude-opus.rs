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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: Vec<i8>)
  requires valid_input(n as int, a@.map(|_i, x| x as int))
  ensures valid_output(result@.map(|_i, x| x as int), n as int, a@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed array bounds and parent index calculation */
    let mut result: Vec<i8> = Vec::new();
    
    let mut k: usize = 1;
    while k < n as usize
        invariant
            n >= 2,
            n <= 127,
            a.len() == n as usize,
            1 <= k <= n as usize,
            result.len() == k - 1,
            forall|j: int| 0 <= j < k - 1 ==> #[trigger] result@[j] as int == count_violations_for_k(a@.map(|_i, x| x as int), n as int, j + 1),
            forall|j: int| 0 <= j < k - 1 ==> #[trigger] result@[j] >= 0,
        decreases (n as usize) - k
    {
        let mut count: i8 = 0;
        let mut i: usize = 2;
        
        while i <= n as usize
            invariant
                n >= 2,
                n <= 127,
                a.len() == n as usize,
                2 <= i <= (n as usize) + 1,
                1 <= k < n as usize,
                count >= 0,
                count as int == Set::new(|j: int| 2 <= j < i as int && {
                    let parent_idx = (j + k as int - 2) / k as int;
                    parent_idx >= 1 && a@.map(|_i, x| x as int)[j-1] < a@.map(|_i, x| x as int)[parent_idx-1]
                }).len(),
            decreases (n as usize) + 1 - i
        {
            if i <= n as usize {
                let parent_idx = (i + k - 2) / k;
                if parent_idx >= 1 && parent_idx <= n as usize && i - 1 < a.len() && parent_idx - 1 < a.len() {
                    if a[i - 1] < a[parent_idx - 1] {
                        count = count + 1;
                    }
                }
            }
            i = i + 1;
        }
        
        result.push(count);
        k = k + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}