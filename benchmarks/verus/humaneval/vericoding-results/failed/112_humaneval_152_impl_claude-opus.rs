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
spec fn abs_value(x: int) -> int {
    if x >= 0 { x } else { -x }
}

// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn compare(game: Vec<i8>, guess: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(game@.map_values(|x: i8| x as int), guess@.map_values(|x: i8| x as int))
    ensures valid_output(game@.map_values(|x: i8| x as int), guess@.map_values(|x: i8| x as int), result@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clause to while loop */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < game.len()
        invariant
            i <= game.len(),
            game.len() == guess.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == abs_value(game@[j] as int - guess@[j] as int),
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
        decreases game.len() - i
    {
        let diff: i8 = game[i] - guess[i];
        let abs_diff: i8 = if diff >= 0 { diff } else { -diff };
        proof {
            assert(abs_diff as int == abs_value(game@[i as int] as int - guess@[i as int] as int));
            assert(0 <= abs_diff as int <= 127);
        }
        result.push(abs_diff);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}