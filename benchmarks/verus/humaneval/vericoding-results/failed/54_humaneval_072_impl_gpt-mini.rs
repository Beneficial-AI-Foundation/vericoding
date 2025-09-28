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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn vec_to_seq(q: Vec<i8>) -> Seq<int>
{
    q@.map(|i: int, x: i8| x as int)
}

/* helper modified by LLM (iteration 5): lemma relating sequence sum to recursive definition */
proof fn lemma_sum_elements_of_vec(q: Vec<i8>)
    ensures
        sum_elements(vec_to_seq(q)) == (if vec_to_seq(q).len() == 0 { 0 } else { vec_to_seq(q)[0] + sum_elements(vec_to_seq(q).subrange(1, vec_to_seq(q).len())) }),
{
    proof {
        reveal(sum_elements);
    }
}

/* helper modified by LLM (iteration 5): lemma relating vec palindrome to is_palindrome */
proof fn lemma_is_palindrome_of_vec(q: Vec<i8>)
    ensures
        is_palindrome(vec_to_seq(q)) == (forall|i: int| 0 <= i < vec_to_seq(q).len() ==> vec_to_seq(q)[i] == vec_to_seq(q)[vec_to_seq(q).len() - 1 - i]),
{
    proof {
        reveal(is_palindrome);
    }
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(q: Vec<i8>, w: i8) -> (result: bool)
    ensures result == (is_palindrome(q@.map(|i: int, x: i8| x as int)) && sum_elements(q@.map(|i: int, x: i8| x as int)) <= w as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute palindrome and sum using tracked spec terms */
    let s: Seq<int> = tracked(vec_to_seq(q));
    let n: int = tracked(q.len() as int);

    let mut i: int = tracked(0);
    let mut pal: bool = true;
    while i < n
        invariant
            0 <= i <= n,
            pal == (forall|k: int| 0 <= k < i ==> s[k] == s[s.len() - 1 - k]),
        decreases n - i
    {
        if q[i as usize] != q[(n - 1 - i) as usize] {
            pal = false;
        }
        i += 1;
    }

    let mut j: int = tracked(0);
    let mut sum: int = tracked(0);
    while j < n
        invariant
            0 <= j <= n,
            sum == sum_elements(s.subrange(0, j)),
        decreases n - j
    {
        sum = sum + q[j as usize] as int;
        j += 1;
    }

    let result = pal && sum <= w as int;

    proof {
        lemma_is_palindrome_of_vec(q.clone());
        lemma_sum_elements_of_vec(q.clone());

        assert(pal == is_palindrome(s));
        assert(sum == sum_elements(s));
        assert(result == (is_palindrome(s) && sum_elements(s) <= w as int));
    }

    result
}
// </vc-code>


}

fn main() {}