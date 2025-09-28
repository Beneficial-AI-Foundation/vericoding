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
fn build_line(stars: usize, diamonds: usize) -> (line: String)
    ensures
        line@ == repeat_char('*', stars as int) + repeat_char('D', diamonds as int) + repeat_char('*', stars as int),
        line@.len() == stars as int + diamonds as int + stars as int,
{
    let mut s = String::new();
    let mut k: usize = 0;
    while k < stars
        invariant
            0 <= k as int,
            k as int <= stars as int,
            s@ == repeat_char('*', k as int)
        decreases (stars - k) as int
    {
        s.push('*');
        k += 1;
    }
    let mut d: usize = 0;
    while d < diamonds
        invariant
            0 <= d as int,
            d as int <= diamonds as int,
            s@ == repeat_char('*', stars as int) + repeat_char('D', d as int)
        decreases (diamonds - d) as int
    {
        s.push('D');
        d += 1;
    }
    let mut t: usize = 0;
    while t < stars
        invariant
            0 <= t as int,
            t as int <= stars as int,
            s@ == repeat_char('*', stars as int) + repeat_char('D', diamonds as int) + repeat_char('*', t as int)
        decreases (stars - t) as int
    {
        s.push('*');
        t += 1;
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
    let magic: int = ((n as int) - 1) / 2;
    let mut res: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            res.len() as int == i as int,
            forall|j: int| 0 <= j < i as int ==> {
                let stars = if j <= magic { magic - j } else { j - magic };
                let diamonds = n as int - 2 * stars;
                #[trigger] res@[j]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
            },
            forall|j: int| 0 <= j < i as int ==> #[trigger] res@[j]@.len() == n as int
        decreases (n - i) as int
    {
        let i_int: int = i as int;
        let stars_i: int = if i_int <= magic { magic - i_int } else { i_int - magic };
        proof {
            if i_int <= magic {
                assert(stars_i >= 0);
                assert(2 * stars_i <= (n as int) - 1);
            } else {
                assert(i_int < n as int);
                assert(stars_i >= 0);
                assert(2 * stars_i <= 2 * ((n as int - 1) - magic));
                assert(2 * ((n as int - 1) - magic) == (n as int) - 1);
                assert(2 * stars_i <= (n as int) - 1);
            }
        }
        let diamonds_i: int = n as int - 2 * stars_i;
        proof { assert(diamonds_i >= 0); }
        let line = build_line(stars_i as usize, diamonds_i as usize);
        proof {
            assert(line@.len() == stars_i + diamonds_i + stars_i);
            assert(stars_i + diamonds_i + stars_i == n as int);
        }
        res.push(line);
        i += 1;
    }
    res
}
// </vc-code>


}

fn main() {}