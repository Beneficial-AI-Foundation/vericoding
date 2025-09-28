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
proof fn lemma_valid_position_constants()
    ensures
        valid_position(0),
        valid_position(1),
        valid_position(2),
{
}

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
    proof { lemma_valid_position_constants(); }
    if n % 2 == 0 {
        let t: i32 = (n / 2) % 3;
        let res: i8 = if t == 0 {
            x
        } else if t == 1 {
            if x == 0 { 2 } else if x == 1 { 0 } else { 1 }
        } else {
            if x == 0 { 1 } else if x == 1 { 2 } else { 0 }
        };
        res
    } else {
        let t: i32 = ((n - 1) / 2) % 3;
        let y: i8 = if x == 0 { 1 } else if x == 1 { 0 } else { 2 };
        let res: i8 = if t == 0 {
            y
        } else if t == 1 {
            if y == 0 { 1 } else if y == 1 { 2 } else { 0 }
        } else {
            if y == 0 { 2 } else if y == 1 { 0 } else { 1 }
        };
        res
    }
}
// </vc-code>


}

fn main() {}