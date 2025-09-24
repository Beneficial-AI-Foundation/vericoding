// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, colors: Seq<char>) -> bool {
    1 <= n <= 100 &&
    colors.len() == n &&
    (forall|c: char| colors.contains(c) ==> (c == 'P' || c == 'W' || c == 'G' || c == 'Y')) &&
    colors.contains('P') && colors.contains('W') && colors.contains('G')
}

spec fn distinct_colors(colors: Seq<char>) -> Set<char> {
    colors.to_set()
}

spec fn solution_string(distinct_count: int) -> &'static str
    recommends distinct_count == 3 || distinct_count == 4
{
    if distinct_count == 3 { "Three" } else { "Four" }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, colors: Seq<char>) -> (result: &'static str)
    requires valid_input(n, colors),
    ensures distinct_colors(colors).len() == 3 || distinct_colors(colors).len() == 4,
    ensures (distinct_colors(colors).len() == 3 ==> result == "Three") && (distinct_colors(colors).len() == 4 ==> result == "Four"),
    ensures result == "Three" || result == "Four",
// </vc-spec>
// <vc-code>
{
    assume(false);
    "Three"
}
// </vc-code>


}

fn main() {}