// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn monotonic(l: Seq<int>) -> bool {
    if l.len() <= 1 {
        true
    } else {
        let increasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] <= l[(i + 1) as int];
        let decreasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] >= l[(i + 1) as int];
        increasing || decreasing
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> for specifications */
spec fn vec_to_seq(v: Vec<i8>) -> Seq<int> {
    v@.map(|_i: int, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn is_monotonic(l: Vec<i8>) -> (result: bool)
    ensures result == monotonic(l@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute monotonic using loop checking adjacent pairs and tracking inc/dec with invariants */
    let n: usize = l.len();
    if n <= 1 {
        true
    } else {
        let mut i: usize = 0;
        let mut inc: bool = true;
        let mut dec: bool = true;
        while i + 1 < n
            invariant
                i < n,
                inc == (forall|j: nat| #![trigger vec_to_seq(l)[j as int]] j < (i as nat) ==> vec_to_seq(l)[j as int] <= vec_to_seq(l)[(j + 1) as int]),
                dec == (forall|j: nat| #![trigger vec_to_seq(l)[j as int]] j < (i as nat) ==> vec_to_seq(l)[j as int] >= vec_to_seq(l)[(j + 1) as int]),
            decreases n - i
        {
            inc = inc && (l[i] <= l[i + 1]);
            dec = dec && (l[i] >= l[i + 1]);
            i += 1;
        }
        let result = inc || dec;
        proof {
            assert(i + 1 >= n);
            assert(i < n);
            assert(i == n - 1);
            assert(inc == (forall|j: nat| #![trigger vec_to_seq(l)[j as int]] j < (n as nat) - 1 ==> vec_to_seq(l)[j as int] <= vec_to_seq(l)[(j + 1) as int]));
            assert(dec == (forall|j: nat| #![trigger vec_to_seq(l)[j as int]] j < (n as nat) - 1 ==> vec_to_seq(l)[j as int] >= vec_to_seq(l)[(j + 1) as int]));
            assert(result == ( (forall|j: nat| #![trigger vec_to_seq(l)[j as int]] j < (n as nat) - 1 ==> vec_to_seq(l)[j as int] <= vec_to_seq(l)[(j + 1) as int]) || (forall|j: nat| #![trigger vec_to_seq(l)[j as int]] j < (n as nat) - 1 ==> vec_to_seq(l)[j as int] >= vec_to_seq(l)[(j + 1) as int]) ));
            assert(result == monotonic(vec_to_seq(l)));
        }
        result
    }
}
// </vc-code>


}

fn main() {}