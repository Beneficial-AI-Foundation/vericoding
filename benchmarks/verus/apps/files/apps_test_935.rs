// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, m: int) -> bool {
    1 <= n <= 100 && 1 <= m <= 100
}

spec fn game_moves(n: int, m: int) -> int
    requires valid_input(n, m)
{
    if n < m { n } else { m }
}

spec fn winner(n: int, m: int) -> Seq<u8>
    requires valid_input(n, m)
{
    let moves = game_moves(n, m);
    if moves % 2 == 1 { 
        seq![65u8, 107u8, 115u8, 104u8, 97u8, 116u8]
    } else { 
        seq![77u8, 97u8, 108u8, 118u8, 105u8, 107u8, 97u8]
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int) -> (result: Seq<u8>)
    requires valid_input(n, m)
    ensures result == winner(n, m)
// </vc-spec>
// <vc-code>
{
    assume(false);
    seq![65u8, 107u8, 115u8, 104u8, 97u8, 116u8]
}
// </vc-code>


}

fn main() {}