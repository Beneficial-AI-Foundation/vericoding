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
{
    let mut count: i8 = 0;
    let mut i: usize = 1;
    
    while i < n as usize
        invariant
            n >= 1,
            s@.len() == n as int,
            0 <= i <= n as int,
            0 <= count <= i as i8 - 1,
            count as int == count_adjacent_same_pairs_up_to(s@, i as int),
        decreases n as int - i as int
    {
        if s[i] == s[i - 1] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}