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
fn abs_i32(x: i32) -> (res: i32)
    ensures
        res >= 0,
        res == abs_value(x as int)
{
    if x >= 0 {
        x
    } else {
        -x
    }
}
// </vc-helpers>

// <vc-spec>
fn compare(game: Vec<i8>, guess: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(game@.map_values(|x: i8| x as int), guess@.map_values(|x: i8| x as int))
    ensures valid_output(game@.map_values(|x: i8| x as int), guess@.map_values(|x: i8| x as int), result@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed return statement by adding 'result' after the loop */
    let len = game.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == abs_value(game@[j] as int - guess@[j] as int) as i8,
        decreases (len - i)
    {
        let game_val = game[i] as i32;
        let guess_val = guess[i] as i32;
        let diff = game_val - guess_val;
        let abs_diff = if diff >= 0 { diff } else { -diff };
        result.push(abs_diff as i8);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}