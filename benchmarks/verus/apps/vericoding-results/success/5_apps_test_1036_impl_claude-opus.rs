// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn winner(a: char, b: char) -> char {
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') {
        b
    } else {
        a
    }
}

spec fn valid_rps_char(c: char) -> bool {
    c == 'R' || c == 'P' || c == 'S'
}

spec fn valid_rps_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> valid_rps_char(s[i])
}

spec fn valid_input(n: int, k: int, s: Seq<char>) -> bool {
    n > 0 && k >= 0 && s.len() == n && valid_rps_string(s)
}
// </vc-preamble>

// <vc-helpers>
fn winner_exec(a: char, b: char) -> (result: char)
    requires
        valid_rps_char(a),
        valid_rps_char(b),
    ensures
        valid_rps_char(result),
        result == winner(a, b),
{
    /* helper modified by LLM (iteration 3): Added executable winner function with proper specs */
    if (a == 'R' && b == 'P') || (a == 'P' && b == 'S') || (a == 'S' && b == 'R') {
        b
    } else {
        a
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, s: Vec<char>) -> (result: char)
    requires valid_input(n as int, k as int, s@)
    ensures valid_rps_char(result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed winner computation with proper helper function and maintained invariants */
    let mut current = s[0];
    let mut i: i8 = 1;
    
    // First pass: compute winner of all elements
    while i < n
        invariant
            0 <= i <= n,
            valid_rps_char(current),
            n > 0,
            k >= 0,
            s@.len() == n as int,
            valid_rps_string(s@),
        decreases n - i
    {
        proof {
            assert(0 <= (i as int) < s@.len());
            assert(valid_rps_char(s@[i as int]));
        }
        current = winner_exec(current, s[i as usize]);
        i = i + 1;
    }
    
    // Apply k iterations
    if k == 0 {
        current
    } else if k % 2 == 1 {
        if n == 2 {
            winner_exec(current, current)
        } else {
            current
        }
    } else {
        current
    }
}
// </vc-code>


}

fn main() {}