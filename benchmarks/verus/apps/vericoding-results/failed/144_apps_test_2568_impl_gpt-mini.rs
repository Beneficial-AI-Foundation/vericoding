// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == '+' || s[i] == '-'
}

spec fn compute_result(s: Seq<char>) -> int {
    compute_result_helper(s, 0, 0, 0, s.len() as int)
}

spec fn compute_result_helper(s: Seq<char>, i: int, cur: int, pm: int, ans: int) -> int
    decreases s.len() - i when 0 <= i <= s.len()
{
    if i == s.len() {
        ans
    } else if s[i] == '+' {
        compute_result_helper(s, i + 1, cur + 1, pm, ans)
    } else {
        let new_cur = cur - 1;
        if new_cur < pm {
            compute_result_helper(s, i + 1, new_cur, new_cur, ans + i + 1)
        } else {
            compute_result_helper(s, i + 1, new_cur, pm, ans)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma to unfold one step of compute_result_helper */
proof fn compute_result_unfold(s: Seq<char>, i: int, cur: int, pm: int, ans: int)
    requires
        0 <= i && i < s.len(),
    ensures
        compute_result_helper(s, i, cur, pm, ans) ==
            if s[i] == '+' {
                compute_result_helper(s, i + 1, cur + 1, pm, ans)
            } else {
                let new_cur = cur - 1;
                if new_cur < pm {
                    compute_result_helper(s, i + 1, new_cur, new_cur, ans + i + 1)
                } else {
                    compute_result_helper(s, i + 1, new_cur, pm, ans)
                }
            },
{
    proof {
        // By the definition of compute_result_helper the above equality holds
        // for any 0 <= i < s.len(). The spec-function definition provides
        // the necessary unfolding, so no additional proof steps are required
        // here.
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires 
        valid_input(s@),
        s.len() <= 127
    ensures 
        result as int >= s@.len(),
        result as int == compute_result(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterative implementation using tracked ghost state and a parallel runtime accumulator */
    let n_usize: usize = s.len();

    let tracked n: int = n_usize as int;
    let mut tracked i: int = 0;
    let mut tracked cur: int = 0;
    let mut tracked pm: int = 0;
    let mut tracked ans: int = n;

    let mut i_usize: usize = 0usize;
    let mut result_usize: usize = n_usize;

    while i_usize < n_usize
        invariant
            0 <= i && i <= n,
            ans == result_usize as int,
            compute_result_helper(s@, i, cur, pm, ans) == compute_result(s@),
        decreases n - i
    {
        proof {
            assert(0 <= i && i < n);
            compute_result_unfold(s@, i, cur, pm, ans);
        }

        if s[i_usize] == '+' {
            cur = cur + 1;
            i = i + 1;
            i_usize = i_usize + 1;
        } else {
            let new_cur = cur - 1;
            cur = new_cur;
            if new_cur < pm {
                pm = new_cur;
                ans = ans + i + 1;
                result_usize = result_usize + (i_usize + 1);
            }
            i = i + 1;
            i_usize = i_usize + 1;
        }
    }

    let result: i8 = result_usize as i8;
    result
}

// </vc-code>


}

fn main() {}