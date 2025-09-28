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
fn get_winner_string(h: int, a: int, b: int) -> (res: Vec<char>)
    requires
        a > 0,
        b > 0,
        h >= 0,
    ensures
        ({
            let total = a + b;
            let k = if h == 0 { 0 } else { h % total };
            (res@ =~= seq!['V', 'a', 'n', 'y', 'a'] <==> determine_winner(k, a, b) == 0) &&
            (res@ =~= seq!['V', 'o', 'v', 'a'] <==> determine_winner(k, a, b) == 1) &&
            (res@ =~= seq!['B', 'o', 't', 'h'] <==> determine_winner(k, a, b) == 2)
        }),
        valid_output(seq![res], 1),
{
    let total = a + b;
    let k = if h == 0 {
        0
    } else {
        proof {
            vstd::arithmetic::mod_internals::lemma_mod_is_nonneg(h, total);
        }
        h % total
    };

    if k <= a {
        vec!['V', 'a', 'n', 'y', 'a']
    } else {
        vec!['V', 'o', 'v', 'a']
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, mobs: Vec<i8>) -> (result: Vec<Vec<char>>)
    requires valid_input(n as int, a as int, b as int, mobs@.map_values(|x: i8| x as int))
    ensures correct_result(result@, n as int, a as int, b as int, mobs@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i <= n,
            valid_input(n as int, a as int, b as int, mobs@.map_values(|x: i8| x as int)),
            result@.len() == i as int,
            valid_output(result@, i as int),
            forall|j: int| 0 <= j < i as int ==> {
                let total = (a as int) + (b as int);
                let h = mobs@.map_values(|x: i8| x as int)@[j];
                let k = if h == 0 { 0 } else { h % total };
                (#[trigger] result@[j]@ =~= seq!['V', 'a', 'n', 'y', 'a'] <==> determine_winner(k, a as int, b as int) == 0) &&
                (result@[j]@ =~= seq!['V', 'o', 'v', 'a'] <==> determine_winner(k, a as int, b as int) == 1) &&
                (result@[j]@ =~= seq!['B', 'o', 't', 'h'] <==> determine_winner(k, a as int, b as int) == 2)
            },
        decreases n - i
    {
        let h = mobs[i as usize];
        let winner_str = get_winner_string(h as int, a as int, b as int);
        result.push(winner_str);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}