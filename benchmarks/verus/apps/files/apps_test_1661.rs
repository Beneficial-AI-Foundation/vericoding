// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_buyable_games(games: Seq<int>, bills: Seq<int>) -> int
    decreases games.len()
{
    if games.len() == 0 {
        0
    } else if bills.len() == 0 {
        0
    } else if bills[0] >= games[0] {
        1 + count_buyable_games(games.subrange(1, games.len() as int), bills.subrange(1, bills.len() as int))
    } else {
        count_buyable_games(games.subrange(1, games.len() as int), bills)
    }
}

spec fn valid_input(n: int, m: int, games: Seq<int>, bills: Seq<int>) -> bool {
    n >= 1 && m >= 1 &&
    games.len() == n && bills.len() == m &&
    (forall|i: int| 0 <= i < games.len() ==> 1 <= games[i] <= 1000) &&
    (forall|i: int| 0 <= i < bills.len() ==> 1 <= bills[i] <= 1000)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, games: Seq<int>, bills: Seq<int>) -> (result: int)
    requires
        valid_input(n, m, games, bills),
    ensures
        0 <= result <= n,
        result <= m,
        result == count_buyable_games(games, bills),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}