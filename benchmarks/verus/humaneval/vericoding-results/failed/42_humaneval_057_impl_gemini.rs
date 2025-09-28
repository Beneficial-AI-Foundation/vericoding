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
/* helper modified by LLM (iteration 5): [Kept spec fn for i8 to int sequence conversion] */
spec fn to_int_seq(s: Seq<i8>) -> Seq<int> {
    s.map(|_i: int, x: i8| x as int)
}

/* helper modified by LLM (iteration 5): [Added proof block to handle early return] */
fn is_increasing(l: &Vec<i8>) -> (res: bool)
    requires
        l.len() > 1,
    ensures
        res == (forall|k: nat| #![trigger to_int_seq(l@)[k as int]] k < l.len() as nat - 1 ==> to_int_seq(l@)[k as int] <= to_int_seq(l@)[(k + 1) as int]),
{
    let mut i: usize = 0;
    while i < l.len() - 1
        invariant
            l.len() > 1,
            i <= l.len() - 1,
            forall|k: nat| #![trigger to_int_seq(l@)[k as int]] k < i as nat ==> to_int_seq(l@)[k as int] <= to_int_seq(l@)[(k + 1) as int],
        decreases l.len() - 1 - i
    {
        if l[i] > l[i + 1] {
            proof {
                assert(to_int_seq(l@)[i as int] > to_int_seq(l@)[(i + 1) as int]);
            }
            return false;
        }
        i = i + 1;
    }
    true
}

/* helper modified by LLM (iteration 5): [Added proof block to handle early return] */
fn is_decreasing(l: &Vec<i8>) -> (res: bool)
    requires
        l.len() > 1,
    ensures
        res == (forall|k: nat| #![trigger to_int_seq(l@)[k as int]] k < l.len() as nat - 1 ==> to_int_seq(l@)[k as int] >= to_int_seq(l@)[(k + 1) as int]),
{
    let mut i: usize = 0;
    while i < l.len() - 1
        invariant
            l.len() > 1,
            i <= l.len() - 1,
            forall|k: nat| #![trigger to_int_seq(l@)[k as int]] k < i as nat ==> to_int_seq(l@)[k as int] >= to_int_seq(l@)[(k + 1) as int],
        decreases l.len() - 1 - i
    {
        if l[i] < l[i + 1] {
            proof {
                assert(to_int_seq(l@)[i as int] < to_int_seq(l@)[(i + 1) as int]);
            }
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn is_monotonic(l: Vec<i8>) -> (result: bool)
    ensures result == monotonic(l@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [Made control flow explicit to aid verification] */
    if l.len() <= 1 {
        true
    } else {
        if is_increasing(&l) {
            true
        } else {
            is_decreasing(&l)
        }
    }
}
// </vc-code>


}

fn main() {}