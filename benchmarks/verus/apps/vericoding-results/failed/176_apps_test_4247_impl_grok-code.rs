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
spec fn count_up_to(p: Seq<int>, i: int, n: int) -> nat {
    Set::new(|j: int| 0 <= j < i && is_median_of_three(p[j], p[j + 1], p[j + 2])).len()
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
    /* code modified by LLM (iteration 2): removed erroneous assertforall_by line to fix compilation */
    proof {
        assert(p@.len() == n as int);
    }
    let mut count: u8 = 0;
    let mut i: usize = 0;
    while i < (n - 2) as usize
        invariant
            i <= (n - 2) as usize,
            count as nat == count_up_to(p@.map(|idx: int, x: i8| x as int), i as int, n as int),
        decreases
            n - 2 - i as u8,
    {
        let a = p[i];
        let b = p[i + 1];
        let c = p[i + 2];
        if (a < b && b < c) || (a > b && b > c) {
            assert(count < n - 2);
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-code>


}

fn main() {}