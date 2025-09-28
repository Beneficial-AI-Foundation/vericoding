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
/* helper modified by LLM (iteration 5): Add trigger annotations to fix quantifier inference */
fn palindrome_helper(v: Vec<i8>) -> (p: bool)
    ensures p == is_palindrome(v@.map(|i: int, x: i8| x as int))
{
    let mut left = 0isize;
    let mut right = v.len() as isize - 1;
    let mut result = true;
    while left <= right
        invariant
            0 <= left <= v.len() as isize,
            0 <= right < v.len() as isize,
            result == (forall|i: int| #![trigger v@[i], trigger v@[v.len() - 1 - i]] 0 <= i < left ==> v@[i] as int == v@[v.len() - 1 - i] as int),
            result == (forall|i: int| #![trigger v@[i], trigger v@[v.len() - 1 - i]] right < i < v.len() ==> v@[i] as int == v@[v.len() - 1 - i] as int),
            result ==> (forall|i: int| #![trigger v@[i], trigger v@[v.len() - 1 - i]] left <= i <= right ==> v@[i] as int == v@[v.len() - 1 - i] as int)
        decreases right - left
    {
        if v[left as usize] != v[right as usize] {
            result = false;
            break;
        }
        left += 1;
        right -= 1;
    }
    result
}

fn sum_helper(v: Vec<i8>) -> (s: i64)
    ensures s >= 0, s as int == sum_elements(v@.map(|i: int, x: i8| x as int))
{
    let mut sum = 0i64;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum >= 0,
            sum as int == sum_elements(v@.subrange(0, i as int).map(|i: int, x: i8| x as int))
        decreases v.len() - i
    {
        sum += v[i] as i64;
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
/* code modified by LLM (iteration 5): fixed implementation */
{
    let is_pal = palindrome_helper(q.clone());
    let total = sum_helper(q);
    is_pal && total <= w as i64
}
// </vc-code>


}

fn main() {}