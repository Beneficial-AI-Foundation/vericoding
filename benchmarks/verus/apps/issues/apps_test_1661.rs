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
    (forall|i: int| 0 <= i < games.len() ==> #[trigger] games[i] >= 1 && #[trigger] games[i] <= 1000) &&
    (forall|i: int| 0 <= i < bills.len() ==> #[trigger] bills[i] >= 1 && #[trigger] bills[i] <= 1000)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, games: Vec<i8>, bills: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, games@.map(|v: i8| v as int), bills@.map(|v: i8| v as int)),
    ensures 
        0 <= result as int <= n as int,
        result as int <= m as int,
        result as int == count_buyable_games(games@.map(|v: i8| v as int), bills@.map(|v: i8| v as int)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}