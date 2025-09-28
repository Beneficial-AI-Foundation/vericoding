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
/* helper modified by LLM (iteration 5): fixed index bounds and added proof for palindrome check */
fn is_palindrome_vec(s: &Vec<i8>) -> (result: bool)
    ensures result == is_palindrome(s@.map(|i: int, x: i8| x as int))
{
    let len = s.len();
    let mut i = 0;
    while i < len/2
        invariant
            0 <= i <= len/2,
            i < len,
            len-1-i >= 0,
            forall|j: int| #![trigger s@[j]] 0 <= j < i ==> s@[j] as int == s@[len-1-j] as int,
        decreases (len/2 - i) as nat
    {
        if s[i] != s[len-1-i] {
            proof {
                assert(0 <= i < len);
                assert(s@[i] as int != s@[len-1-i] as int);
                assert(!is_palindrome(s@.map(|x| x as int)));
            }
            return false;
        }
        i += 1;
    }
    true
}

/* helper modified by LLM (iteration 5): changed to i64 to prevent overflow and fixed subrange bounds */
fn sum_vec(s: &Vec<i8>) -> (result: i64)
    ensures result as int == sum_elements(s@.map(|i: int, x: i8| x as int))
{
    let mut total: i64 = 0;
    let mut i = 0;
    let len = s.len();
    while i < len
        invariant
            0 <= i <= len,
            0 <= i as int <= len,
            total as int == sum_elements(s@.subrange(0, i as int).map(|j: int, x: i8| x as int)),
        decreases (len - i) as nat
    {
        total = total + (s[i] as i64);
        i += 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(q: Vec<i8>, w: i8) -> (result: bool)
    ensures result == (is_palindrome(q@.map(|i: int, x: i8| x as int)) && sum_elements(q@.map(|i: int, x: i8| x as int)) <= w as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): updated to use i64 sum and proper integer comparison */
{
    let is_pal = is_palindrome_vec(&q);
    let total = sum_vec(&q);
    is_pal && (total as int) <= (w as int)
}
// </vc-code>


}

fn main() {}