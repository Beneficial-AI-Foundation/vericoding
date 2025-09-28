// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, s: Seq<char>) -> bool
{
    n >= 1 && s.len() == n
}

spec fn count_adjacent_same_pairs(s: Seq<char>, n: int) -> int
{
    count_adjacent_same_pairs_up_to(s, n)
}

spec fn count_adjacent_same_pairs_up_to(s: Seq<char>, i: int) -> int
    decreases i
{
    if i <= 1 { 0int }
    else { (if s[i-1] == s[i-2] { 1int } else { 0int }) + count_adjacent_same_pairs_up_to(s, i-1) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [implemented recursive proof and added unfolding lemma] */
proof fn lemma_count_bounds(s: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        0 <= count_adjacent_same_pairs_up_to(s, i),
        i > 0 ==> count_adjacent_same_pairs_up_to(s, i) <= i - 1,
    decreases i
{
    if i > 1 {
        lemma_count_bounds(s, i - 1);
    }
}

/* helper modified by LLM (iteration 2): [added lemma to expand a recursive call] */
proof fn lemma_expand_count(s: Seq<char>, i: int)
    requires
        1 < i <= s.len(),
    ensures
        count_adjacent_same_pairs_up_to(s, i) ==
            (if s[i-1] == s[i-2] { 1int } else { 0int }) + count_adjacent_same_pairs_up_to(s, i-1),
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: Vec<char>) -> (result: i8)
    requires 
        valid_input(n as int, s@),
    ensures 
        result >= 0,
        result <= n - 1,
        result as int == count_adjacent_same_pairs(s@, n as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): [added proof block to maintain loop invariant] */
{
    let mut count: i8 = 0;
    let mut i: i8 = 1;

    while i < n
        invariant
            1 <= i <= n,
            valid_input(n as int, s@),
            count as int == count_adjacent_same_pairs_up_to(s@, i as int),
        decreases n - i
    {
        proof {
            lemma_count_bounds(s@, i as int);
        }

        if s[i as usize] == s[(i - 1) as usize] {
            count = count + 1;
        }

        proof {
            if i < n - 1 {
                lemma_expand_count(s@, (i + 1) as int);
            } else if i == n - 1 {
                lemma_expand_count(s@, n as int);
            }
        }

        i = i + 1;
    }

    proof {
        lemma_count_bounds(s@, n as int);
    }

    count
}

// </vc-code>


}

fn main() {}