// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove problematic lemmas and use proper view syntax */
proof fn sum_to_recursive_lemma(arr: Seq<i64>, n: int)
    requires 0 <= n <= arr.len()
    ensures sum_to(arr) == sum_to(arr.take(n)) + sum_to(arr.skip(n))
    decreases arr.len() - n,
{
    if n < arr.len() {
        let prev = arr.take(n);
        let current = arr[n];
        let rest = arr.skip(n + 1);
        
        sum_to_recursive_lemma(arr, n + 1);
        
        assert(prev.push(current) == arr.take(n + 1));
        assert(prev.push(current) + rest == arr);
        
        assert(sum_to(arr.take(n + 1)) == sum_to(prev) + current);
        assert(sum_to(arr) == sum_to(arr.take(n + 1)) + sum_to(rest));
        assert(sum_to(arr) == sum_to(prev) + current + sum_to(rest));
        assert(sum_to(arr) == sum_to(arr.take(n)) + sum_to(arr.skip(n)));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum(arr: &Vec<i64>) -> (result: i128)

    ensures
        sum_to(arr@) == result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix view syntax and simplify implementation */
{
    let mut total: i128 = 0;
    let mut index: usize = 0;
    let view = View::view(arr);
    
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            total == sum_to(view@.take(index as int)),
    {
        proof {
            sum_to_recursive_lemma(view@, index as int);
        }
        total = total + arr[index] as i128;
        index = index + 1;
    }
    
    proof {
        sum_to_recursive_lemma(view@, arr.len() as int);
    }
    total
}
// </vc-code>

}
fn main() {}