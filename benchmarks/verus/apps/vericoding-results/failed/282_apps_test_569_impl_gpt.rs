// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 1
}

spec fn count_distinct_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): expose components of valid_input for later use */
proof fn lemma_valid_input_props(n: int, s: Seq<char>)
    requires
        valid_input(n, s)
    ensures
        s.len() == n,
        n >= 1,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: i32)
    requires 
        valid_input(n as int, s@)
    ensures 
        n > 26 ==> result == -1,
        n <= 26 ==> result >= 0 && result < n as i32,
        n <= 26 ==> result == s@.len() as i32 - count_distinct_chars(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute duplicates using executable scanning without ghost int arithmetic */
    if n > 26 {
        -1
    } else {
        proof { lemma_valid_input_props(n as int, s@); }
        let mut i: usize = 0;
        let mut distinct: usize = 0;
        let mut seen: Vec<char> = Vec::new();
        while i < n
            invariant
                i <= n,
                seen@.len() == distinct as int,
                seen@.len() <= i as int,
                s@.len() as int == n as int,
            decreases (n - i) as int
        {
            let c = s[i];
            let mut j: usize = 0;
            let seen_len = seen.len();
            let mut contains: bool = false;
            while j < seen_len
                invariant
                    j <= seen_len,
                    s@.len() as int == n as int,
                decreases (seen_len - j) as int
            {
                if seen[j] == c {
                    contains = true;
                    break;
                }
                j += 1;
            }
            if !contains {
                seen.push(c);
                distinct += 1;
            }
            i += 1;
        }
        let result: i32 = (n - distinct) as i32;
        proof {
            assert(seen@.len() as int <= s@.len() as int);
        }
        result
    }
}
// </vc-code>


}

fn main() {}