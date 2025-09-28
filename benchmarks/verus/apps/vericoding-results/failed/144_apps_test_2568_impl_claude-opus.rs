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
    /* code modified by LLM (iteration 5): Fix invariant to properly track compute_result_helper */
    let mut cur: i32 = 0;
    let mut pm: i32 = 0;
    let mut ans: i32 = s.len() as i32;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            valid_input(s@),
            s.len() <= 127,
            ans as int == compute_result_helper(s@, 0, 0, 0, s@.len() as int) - compute_result_helper(s@, i as int, cur as int, pm as int, 0) + s@.len() as int,
            pm <= cur,
            pm <= 0,
            cur >= -(i as int),
            cur <= i as int,
            ans >= s.len() as int,
            ans <= s.len() as int + (s.len() as int * (s.len() as int + 1)) / 2,
        decreases s.len() - i
    {
        if s[i] == '+' {
            cur = cur + 1;
        } else {
            cur = cur - 1;
            if cur < pm {
                pm = cur;
                ans = ans + (i as i32) + 1;
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(i == s.len());
        assert(ans as int == compute_result_helper(s@, 0, 0, 0, s@.len() as int));
        assert(compute_result(s@) == compute_result_helper(s@, 0, 0, 0, s@.len() as int));
    }
    
    ans as i8
}
// </vc-code>


}

fn main() {}