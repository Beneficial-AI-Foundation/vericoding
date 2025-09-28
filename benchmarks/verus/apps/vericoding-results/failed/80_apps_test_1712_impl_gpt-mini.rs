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
/* helper modified by LLM (iteration 5): mapping kind to character sequence */
spec fn name_seq(kind: int) -> Seq<char>
    requires
        0 <= kind && kind <= 2,
{
    if kind == 0 {
        seq!['V','a','n','y','a']
    } else if kind == 1 {
        seq!['V','o','v','a']
    } else {
        seq!['B','o','t','h']
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
    /* code modified by LLM (iteration 5): use machine integers for runtime and ghost proofs for spec-level reasoning */
    let n_usize: usize = n as usize;
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize
        invariant
            i <= n_usize,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                let total = (a as int) + (b as int);
                let mob = mobs@.map_values(|x: i8| x as int)[j];
                let k = if mob == 0 { 0 } else { mob % total };
                let kind = if k <= a as int { 0 } else { 1 };
                (result@[j]@ =~= name_seq(kind))
            },
        decreases n_usize - i
    {
        let xi: i8 = *mobs.get(i).unwrap();
        let xi_i64: i64 = xi as i64;
        let total_i64: i64 = (a as i64) + (b as i64);
        let k_i64: i64 = if xi_i64 == 0 { 0 } else { xi_i64 % total_i64 };
        let kind_i64: i64 = if k_i64 <= (a as i64) { 0 } else { 1 };
        let mut name: Vec<char> = Vec::new();
        if kind_i64 == 0 {
            name.push('V'); name.push('a'); name.push('n'); name.push('y'); name.push('a');
        } else {
            name.push('V'); name.push('o'); name.push('v'); name.push('a');
        }
        proof {
            let mob_spec: int = mobs@.map_values(|x: i8| x as int)[i as int];
            let total_spec: int = (a as int) + (b as int);
            let k_spec: int = if mob_spec == 0 { 0 } else { mob_spec % total_spec };
            let kind_spec_expected: int = if k_spec <= a as int { 0 } else { 1 };
            let kind_spec_actual: int = kind_i64 as int;
            assert(mob_spec == xi as int);
            assert(kind_spec_actual == kind_spec_expected);
            assert(name@ =~= name_seq(kind_spec_expected));
        }
        result.push(name);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}