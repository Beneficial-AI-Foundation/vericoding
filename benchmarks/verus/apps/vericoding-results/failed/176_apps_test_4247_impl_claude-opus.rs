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
    /* code modified by LLM (iteration 3): Fixed sequence indexing by converting usize to int */
    let mut count: u8 = 0;
    let mut i: usize = 0;
    
    while i < (n - 2) as usize
        invariant
            i <= (n - 2) as usize,
            n >= 3,
            p.len() == n as usize,
            count <= i as u8,
            count as nat == Set::new(|j: int| 0 <= j < i as int && is_median_of_three(p@[j] as int, p@[j + 1] as int, p@[j + 2] as int)).len(),
        decreases (n - 2) as usize - i
    {
        let a: i8 = p[i];
        let b: i8 = p[i + 1];
        let c: i8 = p[i + 2];
        
        if (a < b && b < c) || (a > b && b > c) {
            proof {
                assert(is_median_of_three(p@[i as int] as int, p@[(i + 1) as int] as int, p@[(i + 2) as int] as int));
                let old_set = Set::new(|j: int| 0 <= j < i as int && is_median_of_three(p@[j] as int, p@[j + 1] as int, p@[j + 2] as int));
                let new_set = Set::new(|j: int| 0 <= j < (i + 1) as int && is_median_of_three(p@[j] as int, p@[j + 1] as int, p@[j + 2] as int));
                assert(new_set =~= old_set.insert(i as int));
                assert(!old_set.contains(i as int));
            }
            count = count + 1;
        } else {
            proof {
                assert(!is_median_of_three(p@[i as int] as int, p@[(i + 1) as int] as int, p@[(i + 2) as int] as int));
                let old_set = Set::new(|j: int| 0 <= j < i as int && is_median_of_three(p@[j] as int, p@[j + 1] as int, p@[j + 2] as int));
                let new_set = Set::new(|j: int| 0 <= j < (i + 1) as int && is_median_of_three(p@[j] as int, p@[j + 1] as int, p@[j + 2] as int));
                assert(new_set =~= old_set);
            }
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}