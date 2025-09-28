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
/* helper modified by LLM (iteration 2): implemented proof that abs_value is nonnegative */
proof fn abs_nonneg(x: int)
    ensures
        abs_value(x) >= 0,
{
    if x >= 0 {
        assert(abs_value(x) == x);
        assert(x >= 0);
    } else {
        assert(abs_value(x) == -x);
        assert(-x > 0);
        assert(-x >= 0);
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
    /* code modified by LLM (iteration 2): compute absolute differences using i16 to avoid using int in exec code */
    let n = game.len();
    let mut result: Vec<i8> = Vec::new();
    result.reserve(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
        decreases n - i
    {
        let a16: i16 = game[i] as i16;
        let b16: i16 = guess[i] as i16;
        let d: i16 = a16 - b16;
        let abs_d: i16 = if d >= 0 { d } else { -d };
        let r: i8 = if abs_d <= 127 { abs_d as i8 } else { 127i8 };
        result.push(r);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}