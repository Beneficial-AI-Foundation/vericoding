use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// <vc-helpers>
fn abs_int_is_non_negative(x: int)
    ensures
        abs(x) >= 0,
{
    if x < 0 {
        assert(-x >= 0);
    } else {
        assert(x >= 0);
    }
}

fn lemma_abs_sub_is_commutative(a: int, b: int)
    ensures
        abs(a - b) == abs(b - a),
{
    if a - b < 0 {
        assert(abs(a - b) == -(a - b));
    } else {
        assert(abs(a - b) == a - b);
    }

    if b - a < 0 {
        assert(abs(b - a) == -(b - a));
    } else {
        assert(abs(b - a) == b - a);
    }
    assert(-(a - b) == b - a);
    assert(a - b == -(b - a));
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

    let mut i: int = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            forall|x: int, y: int| 0 <= x < i && 0 <= y < numbers.len() && x != y ==> abs(numbers[x] - numbers[y]) >= threshold,
    {
        let mut j: int = i + 1;
        while j < numbers.len()
            invariant
                i < j <= numbers.len(),
                0 <= i < numbers.len(),
                forall|x: int, y: int| 0 <= x < i && 0 <= y < numbers.len() && x != y ==> abs(numbers[x] - numbers[y]) >= threshold,
                forall|y: int| i < y < j && i != y ==> abs(numbers[i] - numbers[y]) >= threshold,
        {
            abs_int_is_non_negative(numbers.index(i) - numbers.index(j)); // Required for non-negative property of abs
            if abs(numbers.index(i) - numbers.index(j)) < threshold {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

fn main() {}

}