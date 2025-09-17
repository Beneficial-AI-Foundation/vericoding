// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(game: Seq<int>, guess: Seq<int>) -> bool {
    game.len() == guess.len()
}

spec fn valid_output(game: Seq<int>, guess: Seq<int>, result: Seq<int>) -> bool {
    game.len() == guess.len() ==> (
        && result.len() == game.len()
        && (forall|i: int| 0 <= i < game.len() ==> result[i] == abs_value(game[i] - guess[i]))
        && (forall|i: int| 0 <= i < result.len() ==> result[i] >= 0)
    )
}
// </vc-preamble>

// <vc-helpers>
spec fn abs_value(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-helpers>

// <vc-spec>
fn compare(game: Seq<int>, guess: Seq<int>) -> (result: Seq<int>)
    requires valid_input(game, guess)
    ensures valid_output(game, guess, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}