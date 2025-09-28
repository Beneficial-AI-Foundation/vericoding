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
/* helper modified by LLM (iteration 5): Fixed nat to int conversion for s.len() */
proof fn lemma_compute_result_bounds(s: Seq<char>, i: int, cur: int, pm: int, ans: int)
    requires
        valid_input(s),
        0 <= i <= s.len(),
        ans >= i,
        pm <= cur
    ensures
        compute_result_helper(s, i, cur, pm, ans) >= s.len()
    decreases s.len() - i
{
    if i == s.len() {
        assert(ans >= i);
        assert(ans >= s.len());
    } else if s[i] == '+' {
        lemma_compute_result_bounds(s, i + 1, cur + 1, pm, ans);
    } else {
        let new_cur = cur - 1;
        if new_cur < pm {
            lemma_compute_result_bounds(s, i + 1, new_cur, new_cur, ans + i + 1);
        } else {
            lemma_compute_result_bounds(s, i + 1, new_cur, pm, ans);
        }
    }
}

proof fn lemma_compute_result_main(s: Seq<char>)
    requires valid_input(s)
    ensures compute_result(s) >= s.len()
{
    lemma_compute_result_bounds(s, 0, 0, 0, s.len() as int);
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
    /* code modified by LLM (iteration 5): Added decreases clause to while loop */
    let mut cur: i32 = 0;
    let mut pm: i32 = 0;
    let mut ans: i32 = s.len() as i32;
    let mut i: usize = 0;
    
    proof {
        lemma_compute_result_main(s@);
    }
    
    while i < s.len()
        invariant
            i <= s.len(),
            ans as int >= s@.len(),
            ans <= 127
        decreases s.len() - i
    {
        if s[i] == '+' {
            cur += 1;
        } else {
            cur -= 1;
            if cur < pm {
                pm = cur;
                ans += (i + 1) as i32;
            }
        }
        i += 1;
    }
    
    ans as i8
}
// </vc-code>


}

fn main() {}