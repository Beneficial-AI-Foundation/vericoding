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
spec fn count_violations_for_k_up_to_i(a: Seq<int>, k: int, i: int) -> int {
  let violations = Set::new(|j: int| 2 <= j < i && {
    let parent_idx = (j + k - 2) / k;
    parent_idx >= 1 && a[j-1] < a[parent_idx-1]
  });
  violations.len() as int
}

/* helper modified by LLM (iteration 4): fixed compilation error by changing `ghost let` to `let ghost` */
fn compute_violations_for_k(n: i8, a: &Vec<i8>, k: i8) -> (violations: i8)
    requires
        valid_input(n as int, a@.map(|_i, x| x as int)),
        1 <= k < n,
    ensures
        violations as int == count_violations_for_k(a@.map(|_i, x| x as int), n as int, k as int),
{
    let ghost a_int = a@.map(|_i, x| x as int);
    let ghost n_int = n as int;
    let ghost k_int = k as int;
    let mut violations: i8 = 0;
    let mut i: i8 = 2;

    while i <= n
        invariant
            valid_input(n_int, a_int),
            a_int === a@.map(|_i, x| x as int),
            1 <= k_int < n_int,
            2 <= i <= n + 1,
            violations as int == count_violations_for_k_up_to_i(a_int, k_int, i as int),
        decreases n - i
    {
        let parent_idx_val = (i as i16 + k as i16 - 2) / (k as i16);
        let parent_idx = parent_idx_val as i8;

        proof {
            let i_int = i as int;
            assert(parent_idx as int == ((i_int + k_int - 2) / k_int));
        }

        let parent_idx_usize = (parent_idx - 1) as usize;
        let i_usize = (i - 1) as usize;

        if a[i_usize] < a[parent_idx_usize] {
            violations = violations + 1;
        }
        
        i = i + 1;
    }

    proof {
        assert(count_violations_for_k_up_to_i(a_int, k_int, n_int + 1) == count_violations_for_k(a_int, n_int, k_int));
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
    /* code modified by LLM (iteration 4): fixed compilation error by changing `ghost let` to `let ghost` */
    let ghost a_int = a@.map(|_i, x| x as int);
    let ghost n_int = n as int;

    let mut result: Vec<i8> = Vec::new();
    let mut k: i8 = 1;

    while k < n
        invariant
            valid_input(n_int, a_int),
            a@.map(|_i, x| x as int) === a_int,
            1 <= k <= n,
            result.view().len() == (k - 1) as nat,
            forall|j: int| 1 <= j < k ==> #[trigger] (result.view()[j-1] as int) == count_violations_for_k(a_int, n_int, j),
        decreases n - k
    {
        let violations = compute_violations_for_k(n, &a, k);
        result.push(violations);
        k = k + 1;
    }

    result
}
// </vc-code>


}

fn main() {}