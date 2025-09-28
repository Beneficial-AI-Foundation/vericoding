// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, p: Seq<int>) -> bool {
    p.len() == n && n >= 3
}

spec fn count_median_elements(p: Seq<int>, n: int) -> nat {
    if valid_input(n, p) {
        Set::new(|i: int| 0 <= i < n - 2 && is_median_of_three(p[i], p[i + 1], p[i + 2])).len()
    } else {
        0
    }
}

spec fn is_median_of_three(a: int, b: int, c: int) -> bool {
    (a < b && b < c) || (a > b && b > c)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): convert Vec<i8> to Seq<int> for ghost reasoning */
spec fn vec_to_seq(p: Vec<i8>) -> Seq<int> {
    p@.map(|i: int, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, p: Vec<i8>) -> (result: u8)
    requires
        valid_input(n as int, p@.map(|i: int, x: i8| x as int)),
    ensures
        result <= n - 2,
        result as nat == count_median_elements(p@.map(|i: int, x: i8| x as int), n as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute runtime count and maintain loop invariant linking to spec */
    let len_usize: usize = n as usize;
    let mut count: u8 = 0;
    let mut i: usize = 0;
    while i < len_usize - 2
        invariant
            0 <= i as int,
            i as int <= n as int - 2,
            count as nat == Set::new(|j: int| 0 <= j < i as int && is_median_of_three(
                p@.map(|k: int, x: i8| x as int)@[j],
                p@.map(|k: int, x: i8| x as int)@[j+1],
                p@.map(|k: int, x: i8| x as int)@[j+2]
            )).len(),
        decreases (n as int - 2) - i as int
    {
        let a = p[i];
        let b = p[i + 1];
        let c = p[i + 2];
        if (a < b && b < c) || (a > b && b > c) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}