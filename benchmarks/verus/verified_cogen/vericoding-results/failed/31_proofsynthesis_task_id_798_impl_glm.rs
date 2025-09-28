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
/* helper modified by LLM (iteration 5): added lemma to prove sum_to property for sequence concatenation */
proof fn sum_to_take_add(s: Seq<i64>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        sum_to(s.take(i + 1)) == sum_to(s.take(i)) + s[i],
{
    // By definition of sum_to:
    // sum_to(s.take(i + 1)) = sum_to(s.take(i + 1).drop_last()) + s.take(i + 1).last()
    // s.take(i + 1).drop_last() = s.take(i)
    // s.take(i + 1).last() = s[i]
    // Therefore: sum_to(s.take(i + 1)) = sum_to(s.take(i)) + s[i]
    assert(s.take(i + 1).drop_last() == s.take(i));
    assert(s.take(i + 1).last() == s[i]);
}
// </vc-helpers>

// <vc-spec>
fn sum(arr: &Vec<i64>) -> (result: i128)

    ensures
        sum_to(arr@) == result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed proof logic and used proper lemma */
{
    let mut total: i128 = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant 
            i <= arr.len(),
            total == sum_to(arr@.take(i as int))
        decreases arr.len() - i
    {
        proof {
            sum_to_take_add(arr@, i as int);
        }
        total = total + (arr[i] as i128);
        i += 1;
    }
    proof {
        assert(i == arr.len());
        assert(arr@.take(i as int) == arr@);
    }
    total
}
// </vc-code>

}
fn main() {}