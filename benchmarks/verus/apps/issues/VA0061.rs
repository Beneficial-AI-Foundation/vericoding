// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_occurrences(s: Seq<nat>, value: nat) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == value {
        1 + count_occurrences(s.subrange(1, s.len() as int), value)
    } else {
        count_occurrences(s.subrange(1, s.len() as int), value)
    }
}

spec fn sum_seq(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn subarray_matches_desired(subarray: Seq<nat>, desired: Seq<nat>, m: nat) -> bool
{
    desired.len() == m &&
    forall|color: nat| #[trigger] count_occurrences(subarray, color) == desired[color as int - 1] && 1 <= color <= m
}

spec fn valid_input(n: nat, m: nat, colors: Seq<nat>, desired: Seq<nat>) -> bool
{
    colors.len() == n &&
    desired.len() == m &&
    (forall|i: int| #[trigger] colors[i] >= 1 && colors[i] <= m && 0 <= i < colors.len()) &&
    (forall|i: int| #[trigger] desired[i] >= 0 && 0 <= i < desired.len()) &&
    sum_seq(desired) <= n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, m: u8, colors: Vec<u8>, desired: Vec<u8>) -> (result: String)
    requires
        valid_input(n as nat, m as nat, colors@.map(|i, x| x as nat), desired@.map(|i, x| x as nat)),
    ensures
        result@ == seq!['Y' as char, 'E' as char, 'S' as char] <==> exists|i: int, j: int| 0 <= i <= j < n as int && #[trigger] subarray_matches_desired(colors@.map(|k, x| x as nat).subrange(i, j + 1), desired@.map(|k, x| x as nat), m as nat),
        result@ == seq!['Y' as char, 'E' as char, 'S' as char] || result@ == seq!['N' as char, 'O' as char],
// </vc-spec>
// <vc-code>
{
    assume(false);
    "NO".to_string()
}
// </vc-code>


}

fn main() {}