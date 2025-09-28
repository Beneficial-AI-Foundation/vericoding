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
/* helper modified by LLM (iteration 5): added range preconditions to function signature */
fn absolute_difference(a: i8, b: i8) -> (result: i8)
    requires
        a as int >= -100,
        a as int <= 100,
        b as int >= -100,
        b as int <= 100,
        abs_value(a as int - b as int) <= 127,
    ensures
        result as int == abs_value(a as int - b as int),
        result >= 0,
{
    if a >= b {
        (a - b) as i8
    } else {
        (b - a) as i8
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
    /* code modified by LLM (iteration 5): added explicit bounds checks to prevent overflow */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < game.len()
        invariant
            i <= game.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == abs_value(game@[j] as int - guess@[j] as int),
            game.len() == guess.len(),
        decreases game.len() - i
    {
        proof {
            assert(game[i] as int >= -128 && game[i] as int <= 127);
            assert(guess[i] as int >= -128 && guess[i] as int <= 127);
            assert(abs_value(game[i] as int - guess[i] as int) <= 255);
        }
        
        let diff = if game[i] >= guess[i] {
            proof {
                assert(game[i] >= guess[i]);
                assert(game[i] as int - guess[i] as int >= 0);
                assert(game[i] as int - guess[i] as int <= 255);
            }
            (game[i] - guess[i])
        } else {
            proof {
                assert(game[i] < guess[i]);
                assert(guess[i] as int - game[i] as int > 0);
                assert(guess[i] as int - game[i] as int <= 255);
            }
            (guess[i] - game[i])
        };
        result.push(diff);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}