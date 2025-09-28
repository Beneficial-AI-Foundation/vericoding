// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_palindrome(s: Seq<int>) -> bool {
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> s[i] == s[s.len() - 1 - i]
}

spec fn sum_elements(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_elements(s.subrange(1, s.len() as int))
    }
}

// </vc-preamble>

// <vc-helpers>
spec fn mapped_seq_of(q: Vec<i8>) -> Seq<int> {
    q@.map(|i: int, x: i8| x as int)
}

exec fn lemma_sum_computation(v: Vec<i8>) -> (result: i8)
    ensures
        result as int == v@.fold_left(0, |acc: int, x: i8| acc + x as int),
        result as int == sum_elements(v@.map(|i: int, x: i8| x as int)),
{
    let mut sum = 0i8;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            sum as int == v@.subrange(0, i as int).fold_left(0, |acc: int, x: i8| acc + x as int),
    {
        sum += v[i];
        i += 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(q: Vec<i8>, w: i8) -> (result: bool)
    ensures result == (is_palindrome(q@.map(|i: int, x: i8| x as int)) && sum_elements(q@.map(|i: int, x: i8| x as int)) <= w as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved loop logic to helper function to avoid proof-mode compilation error */
    
    // Check if palindrome
    let mut is_pal = true;
    let mut i: usize = 0;
    while i < q.len() / 2
        invariant
            i <= q.len() / 2,
            is_pal == forall|k: int| #![trigger mapped_seq_of(q)[k]] 0 <= k < i ==> mapped_seq_of(q)[k] == mapped_seq_of(q)[mapped_seq_of(q).len() - 1 - k],
    {
        if q[i] != q[q.len() - 1 - i] {
            is_pal = false;
            break;
        }
        i += 1;
    }
    
    if !is_pal {
        return false;
    }
    
    // Check sum using helper
    let sum = lemma_sum_computation(q);
    
    is_pal && sum <= w
}
// </vc-code>


}

fn main() {}