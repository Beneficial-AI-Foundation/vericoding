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
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing 'lemma' keyword repetition */
proof fn lemma_determine_winner_bounds(k: int, a: int, b: int)
    requires a > 0, b > 0
    ensures determine_winner(k, a, b) == 0 || determine_winner(k, a, b) == 1
{
}

proof fn lemma_mod_zero_case(mob: int, total: int)
    requires mob == 0, total > 0
    ensures mob % total == 0
{
}

proof fn lemma_mod_properties(mob: int, total: int)
    requires mob > 0, total > 0
    ensures 0 <= mob % total < total
{
}

fn create_vanya_string() -> (result: Vec<char>)
    ensures result@ =~= seq!['V', 'a', 'n', 'y', 'a']
{
    vec!['V', 'a', 'n', 'y', 'a']
}

fn create_vova_string() -> (result: Vec<char>)
    ensures result@ =~= seq!['V', 'o', 'v', 'a']
{
    vec!['V', 'o', 'v', 'a']
}

fn create_both_string() -> (result: Vec<char>)
    ensures result@ =~= seq!['B', 'o', 't', 'h']
{
    vec!['B', 'o', 't', 'h']
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, mobs: Vec<i8>) -> (result: Vec<Vec<char>>)
    requires valid_input(n as int, a as int, b as int, mobs@.map_values(|x: i8| x as int))
    ensures correct_result(result@, n as int, a as int, b as int, mobs@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed ghost variable assignment error by using let binding instead */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            i <= n as usize,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let total = a as int + b as int;
                let k = if mobs[j] as int == 0 { 0 } else { mobs[j] as int % total };
                (#[trigger] result[j]@ =~= seq!['V', 'a', 'n', 'y', 'a'] <==> determine_winner(k, a as int, b as int) == 0) &&
                (result[j]@ =~= seq!['V', 'o', 'v', 'a'] <==> determine_winner(k, a as int, b as int) == 1) &&
                (result[j]@ =~= seq!['B', 'o', 't', 'h'] <==> determine_winner(k, a as int, b as int) == 2)
            },
        decreases n as usize - i
    {
        let total = a + b;
        let mob_value = mobs[i] as i8;
        let k = if mob_value == 0 { 0 } else { mob_value % total };
        
        proof {
            lemma_determine_winner_bounds(k as int, a as int, b as int);
            if mob_value == 0 {
                lemma_mod_zero_case(mob_value as int, total as int);
            } else {
                lemma_mod_properties(mob_value as int, total as int);
            }
            let ghost winner = determine_winner(k as int, a as int, b as int);
        }
        
        if k <= a {
            result.push(create_vanya_string());
        } else {
            result.push(create_vova_string());
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}