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
/* helper modified by LLM (iteration 3): Removed broken cycle lemma, kept only valid involution lemma */
proof fn lemma_swap_involution(pos: int, move_num: int)
    requires valid_position(pos)
    ensures 
        valid_position(swap_move(pos, move_num)),
        swap_move(swap_move(pos, move_num), move_num) == pos,
{
    // Proof by cases on pos and move_num
    if move_num % 2 == 1 {
        if pos == 0 {
            assert(swap_move(pos, move_num) == 1);
            assert(swap_move(1, move_num) == 0);
        } else if pos == 1 {
            assert(swap_move(pos, move_num) == 0);
            assert(swap_move(0, move_num) == 1);
        } else {
            assert(pos == 2);
            assert(swap_move(pos, move_num) == 2);
            assert(swap_move(2, move_num) == 2);
        }
    } else {
        if pos == 0 {
            assert(swap_move(pos, move_num) == 0);
            assert(swap_move(0, move_num) == 0);
        } else if pos == 1 {
            assert(swap_move(pos, move_num) == 2);
            assert(swap_move(2, move_num) == 1);
        } else {
            assert(pos == 2);
            assert(swap_move(pos, move_num) == 1);
            assert(swap_move(1, move_num) == 2);
        }
    }
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
/* code modified by LLM (iteration 3): Fixed move numbering - move 1,3,5... are odd (swap 0↔1), move 2,4,6... are even (swap 1↔2) */
{
    let mut current_pos: i8 = x;
    let cycle = (n % 6) as i32;
    
    // Apply the moves based on the cycle position
    let mut j: i32 = 0;
    while j < cycle
        invariant
            0 <= j <= cycle,
            cycle <= 6,
            valid_position(current_pos as int),
        decreases cycle - j
    {
        let move_num = j + 1; // Move numbers are 1-indexed
        if move_num % 2 == 1 {
            // Odd move (1, 3, 5): swap positions 0 and 1
            if current_pos == 0 {
                current_pos = 1;
            } else if current_pos == 1 {
                current_pos = 0;
            }
            // Position 2 stays at 2
        } else {
            // Even move (2, 4, 6): swap positions 1 and 2
            if current_pos == 1 {
                current_pos = 2;
            } else if current_pos == 2 {
                current_pos = 1;
            }
            // Position 0 stays at 0
        }
        
        j = j + 1;
        
        proof {
            // Verify that current_pos remains valid
            assert(0 <= current_pos <= 2);
            assert(valid_position(current_pos as int));
        }
    }
    
    current_pos
}
// </vc-code>


}

fn main() {}