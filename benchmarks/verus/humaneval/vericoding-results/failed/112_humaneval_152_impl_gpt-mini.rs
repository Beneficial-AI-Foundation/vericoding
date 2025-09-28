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
/* helper modified by LLM (iteration 5): lemma relating abs_value definition */
proof fn abs_value_def_holds(x: int)
    ensures
        abs_value(x) == if x >= 0 { x } else { -x },
{
    // By unfolding the definition of abs_value
    assert(abs_value(x) == if x >= 0 { x } else { -x });
}

/* helper modified by LLM (iteration 5): trivial lemma connecting i8 subtraction to spec ints */
proof fn i8_sub_matches_spec(g: i8, s: i8)
    ensures
        abs_value((g as int) - (s as int)) == if (g as int) - (s as int) >= 0 { (g as int) - (s as int) } else { -((g as int) - (s as int)) },
{
    assert(abs_value((g as int) - (s as int)) == if (g as int) - (s as int) >= 0 { (g as int) - (s as int) } else { -((g as int) - (s as int)) });
}

// </vc-helpers>

// <vc-spec>
fn compare(game: Vec<i8>, guess: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(game@.map_values(|x: i8| x as int), guess@.map_values(|x: i8| x as int))
    ensures valid_output(game@.map_values(|x: i8| x as int), guess@.map_values(|x: i8| x as int), result@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute absolute differences using usize indices and i16 arithmetic */
    let n: usize = game.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
        decreases n - i
    {
        let g: i8 = game[i];
        let s: i8 = guess[i];
        let diff: i16 = (g as i16) - (s as i16);
        let ad: i16 = if diff >= 0 { diff } else { -diff };
        result.push(ad as i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}