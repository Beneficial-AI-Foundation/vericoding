// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 3 && n <= 101 && n % 2 == 1
}

spec fn valid_result(result: Seq<String>, n: int) -> bool {
    result.len() == n &&
    forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i]@.len() == n
}

spec fn repeat_char(c: char, count: int) -> Seq<char>
    decreases count
{
    if count <= 0 { Seq::empty() }
    else { repeat_char(c, count - 1).push(c) }
}

spec fn correct_diamond_pattern(result: Seq<String>, n: int) -> bool {
    result.len() == n ==> {
        let magic = (n - 1) / 2;
        
        (forall|i: int| 0 <= i <= magic && i < result.len() ==> {
            let stars = magic - i;
            let diamonds = n - 2 * stars;
            #[trigger] result[i]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
        }) &&
        
        (forall|i: int| magic + 1 <= i < n && i < result.len() ==> {
            let u = i - magic;
            let stars = u;
            let diamonds = n - 2 * stars;
            #[trigger] result[i]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
        })
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: usize) -> (result: Vec<String>)
    requires 
        valid_input(n as int)
    ensures 
        valid_result(result@, n as int),
        correct_diamond_pattern(result@, n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type handling for `stars` and `diamonds` calculations by keeping them `usize` where possible, and only casting to `int` for `repeat_char` calls. */
{
    let mut result: Vec<String> = Vec::new();
    let magic = (n - 1) / 2;

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result[j]@.len() == n as int,
            forall|j: int| 0 <= j < i as int && j <= magic as int ==> {
                let stars_val = magic as int - j;
                let diamonds_val = n as int - 2 * stars_val;
                #[trigger] result[j]@ == repeat_char('*', stars_val) + repeat_char('D', diamonds_val) + repeat_char('*', stars_val)
            },
            forall|j: int| 0 <= j < i as int && magic as int + 1 <= j ==> {
                let u_val = j - magic as int;
                let stars_val = u_val;
                let diamonds_val = n as int - 2 * stars_val;
                #[trigger] result[j]@ == repeat_char('*', stars_val) + repeat_char('D', diamonds_val) + repeat_char('*', stars_val)
            },
        decreases n - i
    {
        if i <= magic {
            let stars = magic - i;
            let diamonds = n - 2 * stars;
            let line = (repeat_char('*', stars as int) + repeat_char('D', diamonds as int) + repeat_char('*', stars as int)).to_string();
            result.push(line);
        } else {
            let u = i - magic;
            let stars = u;
            let diamonds = n - 2 * stars;
            let line = (repeat_char('*', stars as int) + repeat_char('D', diamonds as int) + repeat_char('*', stars as int)).to_string();
            result.push(line);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}