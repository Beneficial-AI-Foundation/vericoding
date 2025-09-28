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
// Helper function to check if a value is median of three
fn is_median_helper(a: i8, b: i8, c: i8) -> (result: bool)
    ensures
        result == is_median_of_three(a as int, b as int, c as int),
{
    (a < b && b < c) || (a > b && b > c)
}

/* helper modified by LLM (iteration 2): fixed sequence map syntax */
// Lemma to prove properties about the mapped sequence
proof fn lemma_map_preserves_median(p: Seq<i8>, i: int)
    requires
        0 <= i < p.len() - 2,
    ensures
        is_median_of_three(p[i] as int, p[i + 1] as int, p[i + 2] as int) == 
        is_median_of_three(p.map(|j: int, x: i8| x as int)[i], 
                          p.map(|j: int, x: i8| x as int)[i + 1], 
                          p.map(|j: int, x: i8| x as int)[i + 2]),
{
    // The mapping preserves the median property
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
    /* code modified by LLM (iteration 2): fixed sequence map syntax */
    let mut count: u8 = 0;
    let mut i: usize = 0;
    
    while i < (n as usize) - 2
        invariant
            i <= (n as usize) - 2,
            count <= i,
            count as nat == Set::new(|j: int| 0 <= j < i && 
                is_median_of_three(p@.map(|k: int, x: i8| x as int)[j], 
                                  p@.map(|k: int, x: i8| x as int)[j + 1], 
                                  p@.map(|k: int, x: i8| x as int)[j + 2])).len(),
        decreases (n as usize) - 2 - i
    {
        if is_median_helper(p[i], p[i + 1], p[i + 2]) {
            count = count + 1;
        }
        
        proof {
            lemma_map_preserves_median(p@, i as int);
        }
        
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}