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
/* helper modified by LLM (iteration 5): no functional changes */
fn build_string(c: char, count: usize) -> (s: String)
    requires
        count < 102,
    ensures
        s@ == repeat_char(c, count as int),
        s@.len() == count,
{
    let mut s = String::new();
    let mut i: usize = 0;
    while i < count
        invariant
            i <= count,
            s@ == repeat_char(c, i as int),
            s@.len() == i,
        decreases count - i
    {
        s.push(c);
        i = i + 1;
    }
    s
}
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
{
    /* code modified by LLM (iteration 5): added type annotation to fix compilation error */
    let mut result: Vec<String> = Vec::with_capacity(n);
    let ghost n_int = n as int;
    let magic: usize = (n - 1) / 2;
    let ghost magic_int = magic as int;

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            valid_input(n_int),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j]@.len() == n_int,
            forall|j: int| 0 <= j <= magic_int && j < i as int ==> {
                let stars = magic_int - j;
                let diamonds = n_int - 2 * stars;
                #[trigger] result@[j]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
            },
            forall|j: int| magic_int + 1 <= j < i as int ==> {
                let u = j - magic_int;
                let stars = u;
                let diamonds = n_int - 2 * stars;
                #[trigger] result@[j]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
            },
        decreases n - i
    {
        let current_row: String;
        let ghost i_int = i as int;
        if i <= magic {
            let stars_count = magic - i;
            let diamonds_count = n - 2 * stars_count;

            let stars_part = build_string('*', stars_count);
            let diamonds_part = build_string('D', diamonds_count);
            
            let mut row = stars_part.clone();
            row.push_str(diamonds_part.as_str());
            row.push_str(stars_part.as_str());
            current_row = row;

            proof {
                let stars_count_int = magic_int - i_int;
                let diamonds_count_int = n_int - 2 * stars_count_int;
                assert(current_row@ == repeat_char('*', stars_count_int) + repeat_char('D', diamonds_count_int) + repeat_char('*', stars_count_int));
                assert(current_row@.len() == n_int);
            }
        } else {
            let u = i - magic;
            let stars_count = u;
            let diamonds_count = n - 2 * stars_count;

            let stars_part = build_string('*', stars_count);
            let diamonds_part = build_string('D', diamonds_count);

            let mut row = stars_part.clone();
            row.push_str(diamonds_part.as_str());
            row.push_str(stars_part.as_str());
            current_row = row;

            proof {
                let u_int = i_int - magic_int;
                let stars_count_int = u_int;
                let diamonds_count_int = n_int - 2 * stars_count_int;
                assert(current_row@ == repeat_char('*', stars_count_int) + repeat_char('D', diamonds_count_int) + repeat_char('*', stars_count_int));
                assert(current_row@.len() == n_int);
            }
        }
        
        result.push(current_row);
        i = i + 1;
    }

    result
}
// </vc-code>


}

fn main() {}