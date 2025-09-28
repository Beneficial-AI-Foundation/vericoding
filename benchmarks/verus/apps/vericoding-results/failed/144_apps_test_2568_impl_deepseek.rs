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
/* helper modified by LLM (iteration 5): Fixed preconditions and recursive calls for helper lemmas */
proof fn lemma_compute_result_helper_monotonic(s: Seq<char>, i: int, cur: int, pm: int, ans: int)
    requires
        0 <= i <= s.len(),
        pm <= cur,
        ans >= i
    ensures
        compute_result_helper(s, i, cur, pm, ans) >= ans
    decreases s.len() - i
{
    if i < s.len() {
        if s[i] == '+' {
            lemma_compute_result_helper_monotonic(s, i + 1, cur + 1, pm, ans);
        } else {
            let new_cur = cur - 1;
            if new_cur < pm {
                lemma_compute_result_helper_monotonic(s, i + 1, new_cur, new_cur, ans + i + 1);
            } else {
                lemma_compute_result_helper_monotonic(s, i + 1, new_cur, pm, ans);
            }
        }
    }
}

/* helper modified by LLM (iteration 5): Fixed preconditions and recursive calls for helper lemmas */
proof fn lemma_compute_result_helper_bounds(s: Seq<char>, i: int, cur: int, pm: int, ans: int)
    requires
        0 <= i <= s.len(),
        pm <= cur,
        ans >= i
    ensures
        compute_result_helper(s, i, cur, pm, ans) >= i
    decreases s.len() - i
{
    if i < s.len() {
        if s[i] == '+' {
            lemma_compute_result_helper_bounds(s, i + 1, cur + 1, pm, ans);
        } else {
            let new_cur = cur - 1;
            if new_cur < pm {
                lemma_compute_result_helper_bounds(s, i + 1, new_cur, new_cur, ans + i + 1);
            } else {
                lemma_compute_result_helper_bounds(s, i + 1, new_cur, pm, ans);
            }
        }
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
    /* code modified by LLM (iteration 5): Fixed loop invariants and added proper preconditions for lemma calls */
    let mut cur: i8 = 0;
    let mut pm: i8 = 0;
    let n = s.len() as i8;
    let mut ans: i8 = n;
    let mut i: i8 = 0;
    
    proof {
        assert(n as usize == s.len());
    }
    
    while i < n
        invariant
            0 <= i <= n,
            pm <= cur,
            ans >= i,
            compute_result_helper(s@, i as int, cur as int, pm as int, ans as int) == compute_result(s@)
        decreases n - i
    {
        let idx = i as usize;
        assert(0 <= idx < s.len()) by {
            assert(i >= 0 && i < n);
        }
        
        if s[idx] == '+' {
            cur += 1;
        } else {
            cur -= 1;
            if cur < pm {
                pm = cur;
                ans += i + 1;
            }
        }
        
        proof {
            lemma_compute_result_helper_monotonic(s@, i as int, cur as int, pm as int, ans as int);
            lemma_compute_result_helper_bounds(s@, i as int, cur as int, pm as int, ans as int);
        }
        
        i += 1;
    }
    
    ans
}
// </vc-code>


}

fn main() {}