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

spec fn abs_value_int(x: i8) -> int {
    if x >= 0 { x as int } else { -(x as int) }
}

proof fn abs_value_consistent(x: i8)
    ensures abs_value_int(x) == abs_value(x as int)
{
    if x >= 0 {
        assert(abs_value_int(x) == x as int);
        assert(abs_value(x as int) == x as int);
    } else {
        assert(abs_value_int(x) == -(x as int));
        assert(abs_value(x as int) == -(x as int));
    }
}

proof fn abs_value_nonnegative(x: i8)
    ensures abs_value_int(x) >= 0
{
    if x >= 0 {
        assert(abs_value_int(x) == x as int);
        assert(x as int >= 0);
    } else {
        assert(abs_value_int(x) == -(x as int));
        assert(-(x as int) >= 0);
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
    /* code modified by LLM (iteration 5): Fixed type mismatches by using explicit casts */
    let mut result = Vec::new();
    let len = game.len();
    let mut i: usize = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            result@.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == abs_value_int(game[j] as i8 - guess[j] as i8),
            forall |j: int| 0 <= j < result@.len() ==> result@[j] >= 0
        decreases len - i
    {
        let diff: i8 = game[i] - guess[i];
        let abs_diff: i8 = if diff >= 0 { diff } else { -diff };
        result.push(abs_diff);
        
        abs_value_nonnegative(diff);
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}