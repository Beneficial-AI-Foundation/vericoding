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
/* helper modified by LLM (iteration 2): fix parameter types from nat to int */
proof fn lemma_properties(move_num: int, x: int)
    requires
        valid_position(x),
        0 <= move_num <= 2000000000,
    ensures
        valid_position(swap_move(x, move_num)),
        swap_move(swap_move(x, move_num), move_num) == x,
        reverse_move(x, move_num) == swap_move(x, move_num),
{
    // No recursion needed for this property proof
    assert(reverse_move(x, move_num) == swap_move(x, move_num));
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
/* code modified by LLM (iteration 2): use proper type casting and lemma invocation */
{
    proof {
        lemma_properties(n as int, x as int);
    }
    
    if n % 2 == 1 {
        if x == 0 { 1 } 
        else if x == 1 { 0 }
        else { 2 }
    } else {
        if x == 1 { 2 }
        else if x == 2 { 1 }
        else { 0 }
    }
}
// </vc-code>


}

fn main() {}