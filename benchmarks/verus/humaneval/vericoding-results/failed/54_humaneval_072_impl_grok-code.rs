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
fn compute_sum(v: &Vec<i8>) -> (result: i32)
    requires
        v.len() <= 1000,
    ensures
        result as int == sum_elements(v@.map(|i: int, x: i8| x as int)),
{
    let mut sum = 0i32;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum as int == sum_elements(v@.subrange(0, i as int).map(|j: int, y: i8| y as int)),
        decreases v.len() - i
    {
        sum += v[i] as i32;
        i += 1;
    }
    sum
}

/* helper modified by LLM (iteration 5): changed parameter to &Vec<i8> to avoid moving the vector */

fn is_palindrome_helper(v: &Vec<i8>) -> (result: bool)
    requires
        v.len() <= 1000,
    ensures
        result == (forall|i: int| #![trigger v@[i]] 0 <= i < v@.len() ==> v@[i] as int == v@[v@.len() - 1 - i] as int),
{
    let mut i: usize = 0;
    while i < v.len() / 2
        invariant
            forall|j: int| 0 <= j < i as int ==> v@[j] == v@[v@.len() - 1 - j],
        decreases v.len() - 2 * i
    {
        if v[i] != v[v.len() - 1 - i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(forall|k: int| 0 <= k < v@.len() ==> v@[k] == v@[v@.len() - 1 - k]);
        assert(forall|k: int| 0 <= k < v@.len() ==> v@[k] as int == v@[v@.len() - 1 - k] as int);
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(q: Vec<i8>, w: i8) -> (result: bool)
    ensures result == (is_palindrome(q@.map(|i: int, x: i8| x as int)) && sum_elements(q@.map(|i: int, x: i8| x as int)) <= w as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by passing &q to helpers instead of q */
    let is_pal = is_palindrome_helper(&q);
    let sum = compute_sum(&q);
    is_pal && (sum <= w as i32)
}
// </vc-code>


}

fn main() {}