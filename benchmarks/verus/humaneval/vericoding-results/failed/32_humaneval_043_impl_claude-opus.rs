// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_pair_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < j < l.len() && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn pairs_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_pair_sum_to_zero(l@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by using i8 arithmetic instead of int conversion */
    let n = l.len();
    for i in 0..n
        invariant
            forall|i1: int, j1: int| 0 <= i1 < i as int && i1 < j1 < n as int ==> l@[i1] as int + l@[j1] as int != 0
    {
        for j in (i + 1)..n
            invariant
                forall|j1: int| (i as int) < j1 < j as int ==> l@[i as int] as int + l@[j1] as int != 0
        {
            if l[i] + l[j] == 0i8 {
                proof {
                    assert(0 <= i < j < l@.len());
                    assert(l@.map(|i2: int, x: i8| x as int)[i as int] == l@[i as int] as int);
                    assert(l@.map(|i2: int, x: i8| x as int)[j as int] == l@[j as int] as int);
                    assert(l[i] as int + l[j] as int == 0);
                    assert(has_pair_sum_to_zero(l@.map(|i2: int, x: i8| x as int)));
                }
                return true;
            }
        }
    }
    proof {
        assert(!has_pair_sum_to_zero(l@.map(|i: int, x: i8| x as int))) by {
            assert(forall|i1: int, j1: int| 0 <= i1 < j1 < n as int ==> l@[i1] as int + l@[j1] as int != 0);
            assert(forall|i1: int, j1: int| 0 <= i1 < j1 < l@.len() ==> l@.map(|i2: int, x: i8| x as int)[i1] + l@.map(|i2: int, x: i8| x as int)[j1] != 0);
        }
    }
    false
}
// </vc-code>


}

fn main() {}