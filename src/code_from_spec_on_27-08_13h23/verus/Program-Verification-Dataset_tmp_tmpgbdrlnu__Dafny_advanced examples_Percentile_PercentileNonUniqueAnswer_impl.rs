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
spec fn sum_upto_increases(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j < a.len()
    recommends forall|k: int| 0 <= k < a.len() ==> a[k] > 0
{
    sum_upto(a, i) < sum_upto(a, j)
}

proof fn prove_sum_upto_increases(a: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] > 0,
    ensures
        sum_upto(a, i) < sum_upto(a, j),
    decreases j - i
{
    if i == j {
        assert(sum_upto(a, i) == a[i]);
        assert(sum_upto(a, j) == a[j]);
        assert(a[i] > 0);
    } else {
        let mid = (i + j) / 2;
        prove_sum_upto_increases(a, i, mid);
        prove_sum_upto_increases(a, mid + 1, j);
        assert(sum_upto(a, i) < sum_upto(a, mid));
        assert(sum_upto(a, mid) < sum_upto(a, j));
    }
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
fn percentile_non_unique_answer() -> (result: (int, Vec<int>, int, int, int))
    ensures
        forall|i: int| 0 <= i < result.1@.len() ==> result.1@[i] > 0,
        0 <= result.0 && result.0 <= 100,
        result.2 == sum(result.1@),
        result.2 > 0,
        -1 <= result.3 && result.3 < result.1@.len(),
        sum_upto(result.1@, result.3) <= ((result.0 as int) * result.2) / 100,
        result.3 + 1 < result.1@.len() ==> sum_upto(result.1@, result.3 + 1) >= ((result.0 as int) * result.2) / 100,
        -1 <= result.4 && result.4 < result.1@.len(),
        sum_upto(result.1@, result.4) <= ((result.0 as int) * result.2) / 100,
        result.4 + 1 < result.1@.len() ==> sum_upto(result.1@, result.4 + 1) >= ((result.0 as int) * result.2) / 100,
        result.3 != result.4,
{
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    let total = 6; // sum of v = 1 + 2 + 3
    (50, v, total, 0, 1)
}
// </vc-code>

// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right

fn main() {
}

}