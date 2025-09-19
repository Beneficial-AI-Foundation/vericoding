// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_position(pos: int) -> bool {
    0 <= pos <= 2
}

spec fn swap_move(pos: int, move_num: int) -> int {
    if move_num % 2 == 1 {
        if pos == 0 { 1 }
        else if pos == 1 { 0 }
        else { 2 }
    } else {
        if pos == 1 { 2 }
        else if pos == 2 { 1 }
        else { 0 }
    }
}

spec fn reverse_move(pos: int, move_num: int) -> int {
    if move_num % 2 == 1 {
        if pos == 0 { 1 }
        else if pos == 1 { 0 }
        else { 2 }
    } else {
        if pos == 1 { 2 }
        else if pos == 2 { 1 }
        else { 0 }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn shell_game(n: i32, x: i8) -> (result: i8)
    requires 
        n >= 1 && n <= 2000000000,
        valid_position(x as int),
    ensures valid_position(result as int),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}