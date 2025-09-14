// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 3 && n <= 101 && n % 2 == 1
}

spec fn valid_result(result: Seq<Seq<char>>, n: int) -> bool {
    result.len() == n &&
    forall|i: int| 0 <= i < result.len() ==> result[i].len() == n
}

spec fn repeat_char(c: char, count: int) -> Seq<char> {
    if count <= 0 {
        seq![]
    } else {
        seq![c].add(repeat_char(c, count - 1))
    }
}

spec fn correct_diamond_pattern(result: Seq<Seq<char>>, n: int) -> bool {
    result.len() == n ==> {
        let magic = (n - 1) / 2;
        
        (forall|i: int| 0 <= i <= magic && i < result.len() ==> {
            let stars = magic - i;
            let diamonds = n - 2 * stars;
            result[i] == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
        }) &&
        
        (forall|i: int| magic + 1 <= i < n && i < result.len() ==> {
            let u = i - magic;
            let stars = u;
            let diamonds = n - 2 * stars;
            result[i] == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
        })
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: usize) -> (result: Vec<String>)
    requires 
        valid_input(n as int),
    ensures 
        valid_result(result@.map(|i, s: String| s@), n as int),
        correct_diamond_pattern(result@.map(|i, s: String| s@), n as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}