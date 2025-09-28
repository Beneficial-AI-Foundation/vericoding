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
/* helper modified by LLM (iteration 5): Fixed invariant_lemma to properly handle the proof */
proof fn invariant_lemma(p: Seq<int>, i: int, count: nat, n: int)
    requires
        p.len() == n,
        n >= 3,
        0 <= i <= n - 2,
        count == Set::new(|j: int| 0 <= j < i && is_median_of_three(p[j], p[j + 1], p[j + 2])).len()
    ensures
        count <= count_median_elements(p, n)
{
    if i == n - 2 {
        let full_set = Set::new(|j: int| 0 <= j < n - 2 && is_median_of_three(p[j], p[j + 1], p[j + 2]));
        assert(count == full_set.subset_of(|j: int| 0 <= j < i).len());
    }
}

fn count_median_in_triple(a: i8, b: i8, c: i8) -> bool {
    (a < b && b < c) || (a > b && b > c)
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
/* code modified by LLM (iteration 5): Fixed loop bounds and invariant */
{
    let mut count: u8 = 0;
    let n_usize = n as usize;
    
    if n_usize < 3 {
        return 0;
    }
    
    let mut i: usize = 0;
    
    while i <= n_usize - 3
        invariant
            0 <= i <= n_usize - 2,
            count as nat == Set::new(|j: int| 0 <= j < i as int && is_median_of_three(
                p@.map(|k: int, x: i8| x as int)[j], 
                p@.map(|k: int, x: i8| x as int)[j + 1], 
                p@.map(|k: int, x: i8| x as int)[j + 2]
            )).len()
        decreases (n_usize - i)
    {
        let a = p[i];
        let b = p[i + 1];
        let c = p[i + 2];
        
        if count_median_in_triple(a, b, c) {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    invariant_lemma(p@.map(|i: int, x: i8| x as int), (n_usize - 2) as int, count as nat, n as int);
    count
}
// </vc-code>


}

fn main() {}