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
/* helper modified by LLM (iteration 5): [Fixed the return type of abs_val_i8 to return i8, not int, and changed the argument of -x to be i8 as well.] */
spec fn abs_val_i8(x: i8) -> i8 {
    if x >= 0 { x } else { -x as i8 }
}
// </vc-helpers>

// <vc-spec>
fn compare(game: Vec<i8>, guess: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(game@.map_values(|x: i8| x as int), guess@.map_values(|x: i8| x as int))
    ensures valid_output(game@.map_values(|x: i8| x as int), guess@.map_values(|x: i8| x as int), result@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed the indexing issue with Vec which cannot be indexed with @ and should be indexed with .spec_index instead to support the conversion from a Vec to a Seq.] */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < game.len()
        invariant
            0 <= i,
            i <= game.len(),
            game.len() == guess.len(),
            result.len() == i,
            (forall |k: int| 0 <= k < i as int ==> result.len() > k as usize && result@[k as usize] == abs_val_i8(game.spec_index(k as usize) - guess.spec_index(k as usize)))
        decreases game.len() - i
    {
        let diff: i8 = game.spec_index(i) - guess.spec_index(i);
        let abs_diff: i8 = abs_val_i8(diff);
        result.push(abs_diff);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}