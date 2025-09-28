// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int, mobs: Seq<int>) -> bool {
    n >= 0 && a > 0 && b > 0 && mobs.len() == n &&
    forall|i: int| 0 <= i < n ==> #[trigger] mobs[i] >= 0
}

spec fn valid_output(result: Seq<Vec<char>>, n: int) -> bool {
    result.len() == n &&
    forall|i: int| 0 <= i < n ==> 
        (#[trigger] result[i]@ =~= seq!['V', 'a', 'n', 'y', 'a']) || 
        (result[i]@ =~= seq!['V', 'o', 'v', 'a']) || 
        (result[i]@ =~= seq!['B', 'o', 't', 'h'])
}

spec fn determine_winner(k: int, a: int, b: int) -> int {
    if k <= a { 0 } else { 1 }
}

spec fn correct_result(result: Seq<Vec<char>>, n: int, a: int, b: int, mobs: Seq<int>) -> bool
    recommends a > 0 && b > 0 && mobs.len() == n
{
    valid_output(result, n) &&
    forall|i: int| 0 <= i < n ==> {
        let total = a + b;
        let k = if mobs[i] == 0 { 0 } else { mobs[i] % total };
        (#[trigger] result[i]@ =~= seq!['V', 'a', 'n', 'y', 'a'] <==> determine_winner(k, a, b) == 0) &&
        (result[i]@ =~= seq!['V', 'o', 'v', 'a'] <==> determine_winner(k, a, b) == 1) &&
        (result[i]@ =~= seq!['B', 'o', 't', 'h'] <==> determine_winner(k, a, b) == 2)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, mobs: Vec<i8>) -> (result: Vec<Vec<char>>)
    requires valid_input(n as int, a as int, b as int, mobs@.map_values(|x: i8| x as int))
    ensures correct_result(result@, n as int, a as int, b as int, mobs@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatch for `winner` by making it a normal `int` within the `proof` block and then casting the result of `determine_winner` to an `u8` for the `if else` branches. This isn't necessary, but avoids issues if `determine_winner` were to return different type. Here it is unused. The main issue was `winner` being `i8` when its values (0, 1) are compared with `int` literals. Corrected by making winner `int` type in `proof` block.*/
    let mut result: Vec<Vec<char>> = Vec::new();

    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> {
                let mob_k_ghost_val: int = mobs@[j] as int;
                let total_ghost: int = a as int + b as int;
                let k_ghost_val: int = if mob_k_ghost_val == 0 { 0 } else { mob_k_ghost_val % total_ghost };
                (#[trigger] result[j]@ =~= seq!['V', 'a', 'n', 'y', 'a'] <==> determine_winner(k_ghost_val, a as int, b as int) == 0) &&
                (result[j]@ =~= seq!['V', 'o', 'v', 'a'] <==> determine_winner(k_ghost_val, a as int, b as int) == 1) &&
                (result[j]@ =~= seq!['B', 'o', 't', 'h'] <==> determine_winner(k_ghost_val, a as int, b as int) == 2)
            }
        decreases (n - i) as int
    {
        let mob_k_runtime: i8 = mobs[i as usize];

        let winner_val: int;
        proof {
            let total_ghost_val: int = a as int + b as int;
            let mob_k_ghost_val: int = mob_k_runtime as int;
            let k_ghost_val: int = if mob_k_ghost_val == 0 { 0 } else { mob_k_ghost_val % total_ghost_val };
            winner_val = determine_winner(k_ghost_val, a as int, b as int);
        }

        if winner_val == 0 {
            result.push(vec!['V', 'a', 'n', 'y', 'a']);
        } else {
            result.push(vec!['V', 'o', 'v', 'a']);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}