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
/* helper modified by LLM (iteration 4): [fixed compilation error by correcting the path to the palindrome lemma] */
fn is_palindrome_exec(q: &Vec<i8>) -> (res: bool)
    ensures res == is_palindrome(q@.map(|_i: int, x: i8| x as int)),
{
    let ghost s = q@.map(|_i: int, x: i8| x as int);
    let len = q.len();
    let mut i: usize = 0;
    while i < len / 2
        invariant
            0 <= i && i <= len / 2,
            forall|j: int| 0 <= j < i as int ==> s[j] == s[s.len() - 1 - j],
        decreases len / 2 - i
    {
        if q[i] != q[len - 1 - i] {
            proof {
                let k = i as int;
                assert(s[k] != s[s.len() - 1 - k]);
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        vstd::seq::lemma_is_palindrome_from_half(s);
        assert(is_palindrome(s));
    }
    true
}

/* helper modified by LLM (iteration 2): [fixed compilation error] */
fn sum_elements_exec(q: &Vec<i8>) -> (total: i64)
    ensures total as int == sum_elements(q@.map(|_i: int, x: i8| x as int)),
{
    let ghost s = q@.map(|_i: int, x: i8| x as int);
    let mut i: usize = 0;
    let mut total: i64 = 0;
    while i < q.len()
        invariant
            0 <= i <= q.len(),
            sum_elements(s) == total as int + sum_elements(s.subrange(i as int, s.len() as int)),
        decreases q.len() - i
    {
        total = total + q[i] as i64;
        i = i + 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(q: Vec<i8>, w: i8) -> (result: bool)
    ensures result == (is_palindrome(q@.map(|i: int, x: i8| x as int)) && sum_elements(q@.map(|i: int, x: i8| x as int)) <= w as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [no changes needed, resubmitting] */
    if is_palindrome_exec(&q) {
        let sum = sum_elements_exec(&q);
        sum <= (w as i64)
    } else {
        false
    }
}
// </vc-code>


}

fn main() {}