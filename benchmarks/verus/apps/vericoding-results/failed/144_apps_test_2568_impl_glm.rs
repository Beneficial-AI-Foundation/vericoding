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
/* helper modified by LLM (iteration 5): lemma to unfold one step of compute_result_helper */
lemma compute_result_helper_step(s: Seq<char>, i: int, cur: int, pm: int, ans: int)
    requires 0 <= i < s.len()
    ensures 
        compute_result_helper(s, i, cur, pm, ans) == 
        if s[i] == '+' {
            compute_result_helper(s, i+1, cur+1, pm, ans)
        } else {
            let new_cur = cur - 1;
            if new_cur < pm {
                compute_result_helper(s, i+1, new_cur, new_cur, ans + i + 1)
            } else {
                compute_result_helper(s, i+1, new_cur, pm, ans)
            }
        }
{
    reveal(compute_result_helper);
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
/* code modified by LLM (iteration 5): fixed invariant and used lemma to maintain it */
{
    let n = s.len();
    let mut i: usize = 0;
    let mut cur: isize = 0;
    let mut pm: isize = 0;
    let mut ans: isize = n as isize;

    while i < n
        invariant
            0 <= i as int <= n as int,
            if i < n {
                compute_result_helper(s@, 0, 0, 0, s@.len() as int) == compute_result_helper(s@, i as int, cur as int, pm as int, ans as int)
            } else {
                compute_result_helper(s@, 0, 0, 0, s@.len() as int) == ans as int
            },
        decreases (n - i) as nat
    {
        if s[i] == '+' {
            proof {
                compute_result_helper_step(s@, i as int, cur as int, pm as int, ans as int);
            }
            cur = cur + 1;
            i = i + 1;
        } else {
            let new_cur = cur - 1;
            if new_cur < pm {
                proof {
                    compute_result_helper_step(s@, i as int, cur as int, pm as int, ans as int);
                }
                pm = new_cur;
                ans = ans + (i + 1) as isize;
                cur = new_cur;
                i = i + 1;
            } else {
                proof {
                    compute_result_helper_step(s@, i as int, cur as int, pm as int, ans as int);
                }
                cur = new_cur;
                i = i + 1;
            }
        }
    }

    ans as i8
}
// </vc-code>


}

fn main() {}