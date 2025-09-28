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
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            i <= n as usize,
            result.len() == i,
            n >= 0,
            a > 0,
            b > 0,
            mobs.len() == n as usize,
            forall|j: int| 0 <= j < n as int ==> #[trigger] mobs@[j] >= 0,
            forall|j: int| 0 <= j < i as int ==> {
                let total = (a as int) + (b as int);
                let k = if mobs@[j] == 0 { 0 } else { mobs@[j] % total };
                (#[trigger] result@[j]@ =~= seq!['V', 'a', 'n', 'y', 'a'] <==> determine_winner(k, a as int, b as int) == 0) &&
                (result@[j]@ =~= seq!['V', 'o', 'v', 'a'] <==> determine_winner(k, a as int, b as int) == 1) &&
                (result@[j]@ =~= seq!['B', 'o', 't', 'h'] <==> determine_winner(k, a as int, b as int) == 2)
            },
            forall|j: int| 0 <= j < i as int ==> 
                (#[trigger] result@[j]@ =~= seq!['V', 'a', 'n', 'y', 'a']) || 
                (result@[j]@ =~= seq!['V', 'o', 'v', 'a']) || 
                (result@[j]@ =~= seq!['B', 'o', 't', 'h']),
    {
        let mob_health = mobs[i];
        let total = a + b;
        let k = if mob_health == 0 { 0 } else { (mob_health % total) as i8 };
        
        let winner = if k <= a { 
            let mut v = Vec::new();
            v.push('V');
            v.push('a');
            v.push('n');
            v.push('y');
            v.push('a');
            assert(v@ =~= seq!['V', 'a', 'n', 'y', 'a']);
            v
        } else {
            let mut v = Vec::new();
            v.push('V');
            v.push('o');
            v.push('v');
            v.push('a');
            assert(v@ =~= seq!['V', 'o', 'v', 'a']);
            v
        };
        
        result.push(winner);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}