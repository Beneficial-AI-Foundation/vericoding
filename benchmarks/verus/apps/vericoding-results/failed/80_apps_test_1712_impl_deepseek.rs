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
proof fn mod_properties(k: int, total: int)
    requires total > 0
    ensures 0 <= k % total < total, k % total >= 0
{
    assert(0 <= k % total < total);
}

proof fn index_bound_lemma(len: int, i: int)
    requires 0 <= i < len
    ensures i >= 0 && i < len
{
    assert(i >= 0 && i < len);
}

proof fn subrange_properties(seq: Seq<int>, start: int, end: int)
    requires 0 <= start <= end <= seq@.len()
    ensures seq@.subrange(start, end) =~= seq@.subrange(start, end)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, mobs: Vec<i8>) -> (result: Vec<Vec<char>>)
    requires valid_input(n as int, a as int, b as int, mobs@.map_values(|x: i8| x as int))
    ensures correct_result(result@, n as int, a as int, b as int, mobs@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed auto usage and added proper verification */
    let total = a as i16 + b as i16;
    let mut result = Vec::with_capacity(n as usize);
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            i <= n as usize,
            result@.len() == i,
            0 <= i,
            correct_result(result@, i as int, a as int, b as int, mobs@.subrange(0, i as int).map_values(|x: i8| x as int))
        decreases (n as usize) - i
    {
        proof { index_bound_lemma(mobs@.len() as int, i as int); }
        assert(i < mobs.len());
        let mob = mobs[i] as i16;
        proof { mod_properties(mob as int, total as int); }
        let k = if mob == 0 { 0 } else { mob % total };
        let winner = if k <= a as i16 && k != 0 {
            "Vanya"
        } else if k <= (a as i16 + b as i16) && k > a as i16 {
            "Vova"
        } else {
            "Both"
        };
        
        let result_str = match winner {
            "Vanya" => vec!['V', 'a', 'n', 'y', 'a'],
            "Vova" => vec!['V', 'o', 'v', 'a'],
            _ => vec!['B', 'o', 't', 'h']
        };
        
        result.push(result_str);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}