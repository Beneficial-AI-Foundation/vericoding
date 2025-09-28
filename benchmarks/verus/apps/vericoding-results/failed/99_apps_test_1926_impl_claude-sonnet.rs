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
/* helper modified by LLM (iteration 5): Fixed count_violations_impl to take Vec by reference to avoid move */
proof fn count_violations_non_negative(a: Seq<int>, n: int, k: int)
    requires
        n >= 2,
        a.len() == n,
        1 <= k <= n - 1,
    ensures
        count_violations_for_k(a, n, k) >= 0,
{
}

proof fn count_violations_bounded(a: Seq<int>, n: int, k: int)
    requires
        n >= 2,
        a.len() == n,
        1 <= k <= n - 1,
    ensures
        count_violations_for_k(a, n, k) <= n - 1,
{
}

fn count_violations_impl(a: &Vec<i8>, n: i8, k: i8) -> (count: i8)
    requires
        n >= 2,
        a.len() == n,
        1 <= k <= n - 1,
        a@.len() == n,
    ensures
        count >= 0,
        count == count_violations_for_k(a@.map(|_i, x| x as int), n as int, k as int),
{
    let mut violations = 0i8;
    let mut i = 2i8;
    
    while i <= n
        invariant
            2 <= i <= n + 1,
            violations >= 0,
            violations == Set::new(|j: int| 2 <= j < i && {
                let parent_idx = (j + k as int - 2) / (k as int);
                parent_idx >= 1 && a@[j-1] < a@[parent_idx-1]
            }).len(),
        decreases n - i,
    {
        proof {
            let parent_idx = (i as int + k as int - 2) / (k as int);
        }
        let parent_idx_usize = ((i - 1) as usize + (k - 1) as usize) / (k as usize);
        if parent_idx_usize < (i - 1) as usize && a[(i-1) as usize] < a[parent_idx_usize] {
            violations = violations + 1;
        }
        i = i + 1;
    }
    
    violations
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: Vec<i8>)
  requires valid_input(n as int, a@.map(|_i, x| x as int))
  ensures valid_output(result@.map(|_i, x| x as int), n as int, a@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed to pass Vec by reference to count_violations_impl */
    let mut result: Vec<i8> = Vec::new();
    let mut k = 1i8;
    
    while k <= n - 1
        invariant
            1 <= k <= n,
            result.len() == (k - 1) as nat,
            forall|j: int| 1 <= j < k ==> result@[j-1] >= 0,
            forall|j: int| 1 <= j < k ==> result@[j-1] == count_violations_for_k(a@.map(|_i, x| x as int), n as int, j),
        decreases n - k,
    {
        proof {
            count_violations_non_negative(a@.map(|_i, x| x as int), n as int, k as int);
            count_violations_bounded(a@.map(|_i, x| x as int), n as int, k as int);
        }
        
        let violations = count_violations_impl(&a, n, k);
        result.push(violations);
        k = k + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}