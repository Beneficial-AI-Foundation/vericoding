// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1
}

spec fn count_mismatches_up_to(s: Seq<char>, limit: int) -> int
    decreases limit
{
    if limit <= 0 || s.len() < 1 { 
        0 
    } else {
        let n = s.len() as int - 1;
        let mismatch: int = if limit > 0 && limit <= s.len() && s[limit-1] != s[n - (limit-1)] { 1 } else { 0 };
        count_mismatches_up_to(s, limit-1) + mismatch
    }
}

spec fn count_mismatches(s: Seq<char>) -> int {
    if s.len() >= 1 {
        count_mismatches_up_to(s, s.len() as int)
    } else {
        0
    }
}

spec fn valid_result(s: Seq<char>, result: int) -> bool {
    if valid_input(s) {
        result >= 0 && result <= s.len() / 2 && result == (count_mismatches(s) / 2)
    } else {
        false
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): one-step relation for count_mismatches_up_to with explicit int literals */
proof fn count_mismatches_up_to_succ(s: Seq<char>, k: int)
    requires
        0 <= k && k < s.len() as int,
        s.len() >= 1,
    ensures
        count_mismatches_up_to(s, k+1) == count_mismatches_up_to(s, k) + (if s[k] != s[(s.len() as int - 1 - k)] { 1 as int } else { 0 as int }),
    decreases
        s.len() as int - k
{
    reveal(count_mismatches_up_to);
    let n = s.len() as int - 1;
    // From 0 <= k < s.len() we know k+1 > 0 and k+1 <= s.len() as int
    let mismatch_k: int = if k+1 > 0 && k+1 <= s.len() as int && s[(k+1)-1] != s[n - ((k+1)-1)] { 1 as int } else { 0 as int };
    assert(mismatch_k == (if s[k] != s[n - k] { 1 as int } else { 0 as int }));
    // Unfold the definition of count_mismatches_up_to for k+1 and simplify
    assert(count_mismatches_up_to(s, k+1) ==
        if k+1 <= 0 || s.len() < 1 { 0 as int } else {
            let n_local = s.len() as int - 1;
            let mismatch_local: int = if k+1 > 0 && k+1 <= s.len() as int && s[(k+1)-1] != s[n_local - ((k+1)-1)] { 1 as int } else { 0 as int };
            count_mismatches_up_to(s, (k+1)-1) + mismatch_local
        });
    // Simplify (k+1)-1 to k and mismatch_local to mismatch_k
    assert(count_mismatches_up_to(s, k+1) == count_mismatches_up_to(s, k) + mismatch_k);
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures valid_result(s@, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute mismatches using usize and prove spec using ghost reasoning */
{
    let n: usize = s.len();
    let mut i: usize = 0;
    let mut acc: usize = 0;
    while i < n
        invariant
            i <= n,
            acc as int == count_mismatches_up_to(s@, i as int),
            acc <= i,
        decreases
            (n as int - i as int)
    {
        let j: usize = n - 1 - i;
        let mismatch: usize = if s[i] != s[j] { 1 } else { 0 };
        proof {
            // use the spec lemma for the current i
            count_mismatches_up_to_succ(s@, i as int);
            assert(mismatch as int == (if (s@)[i as int] != (s@)[(n as int - 1 - i as int)] { 1 as int } else { 0 as int }));
        }
        acc = acc + mismatch;
        i = i + 1;
    }
    proof {
        // At loop exit i == n and thus acc == count_mismatches(s@)
        assert(i == n);
        assert(acc as int == count_mismatches_up_to(s@, n as int));
        assert(acc as int == count_mismatches(s@));
    }
    let result_usize: usize = acc / 2;
    let result_i8: i8 = result_usize as i8;
    proof {
        // relate runtime result to specification
        assert(result_i8 as int == (acc as int) / 2);
        assert(acc as int == count_mismatches(s@));
        assert(result_i8 as int == (count_mismatches(s@) / 2));
        // show bounds: 0 <= result <= s.len()/2
        assert(count_mismatches(s@) >= 0);
        assert(acc as int <= n as int);
        assert(result_i8 as int >= 0);
        assert(result_i8 as int <= (n as int) / 2);
    }
    result_i8
}

// </vc-code>


}

fn main() {}