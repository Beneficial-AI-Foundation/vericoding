// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, a: int, b: int, mobs: Seq<int>) -> bool {
    n >= 0 && a > 0 && b > 0 && mobs.len() == n &&
    forall|i: int| 0 <= i < n ==> mobs[i] >= 0
}

spec fn valid_output(result: Seq<Seq<char>>, n: int) -> bool {
    result.len() == n &&
    forall|i: int| 0 <= i < n ==> 
        result[i] == seq!['V', 'a', 'n', 'y', 'a'] ||
        result[i] == seq!['V', 'o', 'v', 'a'] ||
        result[i] == seq!['B', 'o', 't', 'h']
}

spec fn determine_winner(k: int, a: int, b: int) -> int {
    if k == 0 { 2 }
    else if k <= a { 0 }
    else { 1 }
}

spec fn correct_result(result: Seq<Seq<char>>, n: int, a: int, b: int, mobs: Seq<int>) -> bool {
    a > 0 && b > 0 && mobs.len() == n ==>
    valid_output(result, n) &&
    forall|i: int| 0 <= i < n ==> {
        let total = a + b;
        let k = if mobs[i] == 0 { 0 } else { mobs[i] % total };
        (result[i] == seq!['V', 'a', 'n', 'y', 'a'] <==> determine_winner(k, a, b) == 0) &&
        (result[i] == seq!['V', 'o', 'v', 'a'] <==> determine_winner(k, a, b) == 1) &&
        (result[i] == seq!['B', 'o', 't', 'h'] <==> determine_winner(k, a, b) == 2)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: int, b: int, mobs: Seq<int>) -> (result: Seq<Seq<char>>)
    requires valid_input(n, a, b, mobs)
    ensures correct_result(result, n, a, b, mobs)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}