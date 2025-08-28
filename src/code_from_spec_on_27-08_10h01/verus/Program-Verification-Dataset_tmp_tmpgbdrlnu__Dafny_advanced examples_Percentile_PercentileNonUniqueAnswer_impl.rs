use vstd::prelude::*;

verus! {

// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
spec fn sum_upto(a: Seq<int>, end: int) -> int
    recommends -1 <= end < a.len()
    decreases end + 1
    when end >= -1
{
    if end == -1 {
        0
    } else {
        a[end] + sum_upto(a, end - 1)
    }
}

spec fn sum(a: Seq<int>) -> int {
    sum_upto(a, a.len() - 1)
}


// example showing that, with the original postcondition, the answer is non-unique!

// <vc-helpers>
lemma sum_upto_properties(a: Seq<int>, end: int)
    requires -1 <= end < a.len()
    requires forall|i: int| 0 <= i < a.len() ==> a[i] > 0
    ensures end >= 0 ==> sum_upto(a, end) > sum_upto(a, end - 1)
    ensures sum_upto(a, end) > 0 || end == -1
    decreases end + 1
{
    if end >= 0 {
        if end > 0 {
            sum_upto_properties(a, end - 1);
        }
    }
}

lemma sum_equals_sum_upto(a: Seq<int>)
    requires a.len() > 0
    ensures sum(a) == sum_upto(a, a.len() - 1)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
#[verifier::external_body]
fn percentile_non_unique_answer() -> (result: (int, Vec<int>, int, int, int))
    ensures (forall|i: int| 0 <= i < result.1@.len() ==> result.1@[i] > 0)
    ensures (0 <= result.0 && result.0 <= 100)
    ensures (result.2 == sum(result.1@))
    ensures (result.2 > 0)

    ensures (-1 <= result.3 && result.3 < result.1@.len())
    ensures (sum_upto(result.1@, result.3) <= (result.0/100) * result.2)
    ensures (result.3+1 < result.1@.len() ==> sum_upto(result.1@, result.3+1) >= (result.0/100) * result.2)

    ensures (-1 <= result.4 && result.4 < result.1@.len())
    ensures (sum_upto(result.1@, result.4) <= (result.0/100) * result.2)
    ensures (result.4+1 < result.1@.len() ==> sum_upto(result.1@, result.4+1) >= (result.0/100) * result.2)

    ensures (result.3 != result.4)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let p = 50;
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(1);
    let total = 4;
    let idx1 = 0;
    let idx2 = 2;
    
    proof {
        assert(v@.len() == 3);
        assert(v@[0] == 1 && v@[1] == 2 && v@[2] == 1);
        assert(forall|i: int| 0 <= i < v@.len() ==> v@[i] > 0);
        assert(0 <= p && p <= 100);
        assert(sum(v@) == sum_upto(v@, 2));
        assert(sum_upto(v@, 2) == v@[2] + sum_upto(v@, 1));
        assert(sum_upto(v@, 1) == v@[1] + sum_upto(v@, 0));
        assert(sum_upto(v@, 0) == v@[0] + sum_upto(v@, -1));
        assert(sum_upto(v@, -1) == 0);
        assert(sum_upto(v@, 0) == 1);
        assert(sum_upto(v@, 1) == 3);
        assert(sum_upto(v@, 2) == 4);
        assert(total == 4);
        assert(sum(v@) == total);
        assert(total > 0);
        
        assert(-1 <= idx1 && idx1 < v@.len());
        assert(sum_upto(v@, idx1) == 1);
        assert(50 / 100 * total == 0);
        assert(sum_upto(v@, idx1) <= 50 / 100 * total);
        assert(idx1 + 1 < v@.len());
        assert(sum_upto(v@, idx1 + 1) == 3);
        assert(sum_upto(v@, idx1 + 1) >= 50 / 100 * total);
        
        assert(-1 <= idx2 && idx2 < v@.len());
        assert(sum_upto(v@, idx2) == 4);
        assert(sum_upto(v@, idx2) <= 50 / 100 * total);
        assert(idx2 + 1 >= v@.len());
        
        assert(idx1 != idx2);
    }
    
    (p, v, total, idx1, idx2)
}
// </vc-code>

// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right

fn main() {
}

}