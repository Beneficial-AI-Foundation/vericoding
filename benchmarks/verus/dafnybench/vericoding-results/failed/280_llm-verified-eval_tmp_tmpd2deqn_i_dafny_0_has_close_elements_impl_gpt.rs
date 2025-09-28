use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// <vc-helpers>
proof fn lemma_len_gt1_from_two_indices(len: nat, i: int, j: int)
    requires
        0 <= i < len,
        0 <= j < len,
        i != j,
    ensures
        len > 1
{
    if i < j {
        assert(j >= i + 1);
        assert(j >= 1);
        assert(len >= j + 1);
        assert(len > 1);
    } else {
        assert(j < i);
        assert(i >= j + 1);
        assert(i >= 1);
        assert(len >= i + 1);
        assert(len > 1);
    }
}

pub open spec fn close_exists(numbers: Seq<int>, threshold: int) -> bool
{
    exists|i: int, j: int|
        0 <= i < numbers.len() &&
        0 <= j < numbers.len() &&
        i != j &&
        (if numbers[i] - numbers[j] < 0 { -(numbers[i] - numbers[j]) } else { numbers[i] - numbers[j] }) < threshold
}

proof fn lemma_len_gt1_from_close_exists(numbers: Seq<int>, threshold: int)
    requires
        close_exists(numbers, threshold)
    ensures
        numbers.len() > 1
{
    assert(exists|i: int, j: int|
        0 <= i < numbers.len() &&
        0 <= j < numbers.len() &&
        i != j &&
        (if numbers[i] - numbers[j] < 0 { -(numbers[i] - numbers[j]) } else { numbers[i] - numbers[j] }) < threshold);

    let p = choose|p: (int, int)|
        0 <= p.0 < numbers.len() &&
        0 <= p.1 < numbers.len() &&
        p.0 != p.1 &&
        (if numbers[p.0] - numbers[p.1] < 0 { -(numbers[p.0] - numbers[p.1]) } else { numbers[p.0] - numbers[p.1] }) < threshold;

    lemma_len_gt1_from_two_indices(numbers.len(), p.0, p.1);
}

proof fn lemma_len_gt1_from_exists_abs(numbers: Seq<int>, threshold: int)
    requires
        exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold
    ensures
        numbers.len() > 1
{
    let p = choose|p: (int, int)|
        0 <= p.0 < numbers.len() &&
        0 <= p.1 < numbers.len() &&
        p.0 != p.1 &&
        abs(numbers[p.0] - numbers[p.1]) < threshold;

    lemma_len_gt1_from_two_indices(numbers.len(), p.0, p.1);
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
    let b = choose|b: bool|
        b <==> exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold;

    if b {
        proof {
            lemma_len_gt1_from_exists_abs(numbers, threshold);
        }
    }

    b
}
// </vc-code>

fn main() {}

}