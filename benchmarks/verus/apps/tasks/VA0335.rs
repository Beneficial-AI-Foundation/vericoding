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
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}