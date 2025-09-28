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
/* helper modified by LLM (iteration 5): ensure parent index >= 1 */
proof fn parent_idx_ge1(i: int, k: int)
    requires
        i >= 2 as int,
        k >= 1 as int,
    ensures
        (i + k - 2 as int) / k >= 1 as int,
{
    assert(i + k - 2 as int >= k);
    assert((i + k - 2 as int) / k >= 1 as int);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: Vec<i8>)
  requires valid_input(n as int, a@.map(|_i, x| x as int))
  ensures valid_output(result@.map(|_i, x| x as int), n as int, a@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): executable loops with mirrored tracked proofs to relate runtime counts to spec counts */
    let tracked n_int: int = n as int;
    let tracked a_seq: Seq<int> = a@.map(|_i, x| x as int);

    let n_usize: usize = n as usize;
    let mut res: Vec<i8> = Vec::new();

    let mut k_usize: usize = 1usize;
    let tracked mut k_tr: int = 1 as int;
    while k_usize <= n_usize.saturating_sub(1usize)
        invariant
            1 as int <= k_tr,
            k_tr <= n_int,
            res.len() as int == k_tr - 1 as int,
            (forall|j: int| 1 as int <= j <= res.len() as int ==> (res@)[j-1] as int == count_violations_for_k(a_seq, n_int, j)),
        decreases n_int - k_tr
    {
        let mut cnt_exec: i32 = 0i32;
        let mut i_usize: usize = 2usize;
        let tracked mut i_tr: int = 2 as int;
        let tracked mut cnt_tr: int = 0 as int;

        while i_usize <= n_usize
            invariant
                2 as int <= i_tr,
                i_tr <= n_int + 1 as int,
                cnt_tr == (Set::new(|t: int| 2 as int <= t < i_tr && {
                    let parent_idx = (t + k_tr - 2 as int) / k_tr;
                    parent_idx >= 1 as int && a_seq[t - 1] < a_seq[parent_idx - 1]
                }).len() as int),
            decreases n_int + 1 as int - i_tr
        {
            let parent_idx_usize: usize = (i_usize + k_usize).saturating_sub(2usize) / k_usize;
            if parent_idx_usize >= 1usize && (a[i_usize - 1] as i32) < (a[parent_idx_usize - 1] as i32) {
                cnt_exec = cnt_exec + 1i32;
                proof {
                    // mirror the executable increment in the tracked counter
                    cnt_tr = cnt_tr + 1 as int;
                }
            }

            i_usize = i_usize + 1usize;
            proof {
                i_tr = i_tr + 1 as int;
            }
        }

        proof {
            // after finishing inner loop, cnt_tr equals the spec count for this k
            assert(cnt_tr == count_violations_for_k(a_seq, n_int, k_tr));
            // relate executable count to tracked count
            assert((cnt_exec as int) == cnt_tr);
        }

        res.push(cnt_exec as i8);

        k_usize = k_usize + 1usize;
        proof {
            k_tr = k_tr + 1 as int;
        }
    }

    res
}

// </vc-code>


}

fn main() {}