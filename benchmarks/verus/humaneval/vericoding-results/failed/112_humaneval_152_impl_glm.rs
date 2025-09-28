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
    /* code modified by LLM (iteration 5): removed use of int in non-ghost code */
    let n = game.len();
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            i <= game.len(),
            i <= guess.len(),
            forall|j: int| 0 <= j < i ==> result[j] as int == abs_value(game[j] as int - guess[j] as int),
            forall|j: int| 0 <= j < i ==> 0 <= result[j],
        decreases n - i
    {
        let a = game[i];
        let b = guess[i];
        let diff_i8 = if a >= b { a - b } else { b - a };
        result.push(diff_i8);
        proof {
            let a_int = a as int;
            let b_int = b as int;
            assert(diff_i8 as int == abs_value(a_int - b_int));
            assert(result[i] as int == abs_value(a_int - b_int));
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}