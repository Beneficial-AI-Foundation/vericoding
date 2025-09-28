use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// <vc-helpers>
spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (result: bool)
    ensures
        result <==> exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold,
        result ==> numbers.len() > 1,
// </vc-spec>
// <vc-code>
{
    if numbers.len() <= 1 {
        return false;
    }
    for i in 0..numbers.len().exec()
        invariant
            forall |p: int, q: int| 0 <= p < i && p < q < numbers.len() ==>
                #[trigger] abs(numbers[p] - numbers[q]) >= threshold,
    {
        for j in (i + 1)..numbers.len().exec()
            invariant
                forall |m: int| i + 1 <= m < j ==>
                    #[trigger] abs(numbers[i] - numbers[m]) >= threshold,
        {
            if abs(numbers[i] - numbers[j]) < threshold {
                return true;
            } else {
                proof {
                    assert(abs(numbers[i] - numbers[j]) >= threshold);
                }
            }
        }
        proof {
            assert(forall |m: int| i + 1 <= m < numbers.len() ==>
                #[trigger] abs(numbers[i] - numbers[m]) >= threshold);
        }
    }
    proof {
        assert(forall |x: int, y: int| 0 <= x < numbers.len() && 0 <= y < numbers.len() && x != y ==>
            #[trigger] abs(numbers[x] - numbers[y]) >= threshold);
    }
    false
}
// </vc-code>

fn main() {}

}