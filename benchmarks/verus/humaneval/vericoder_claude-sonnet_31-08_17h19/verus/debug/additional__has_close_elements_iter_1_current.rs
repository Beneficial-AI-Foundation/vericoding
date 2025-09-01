use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
proof fn abs_lemma(x: int)
    ensures abs_spec(x) == if x < 0 { -x } else { x }
{
}

proof fn abs_diff_commute(a: int, b: int)
    ensures abs_spec(a - b) == abs_spec(b - a)
{
    if a - b < 0 {
        assert(b - a > 0);
        assert(abs_spec(a - b) == -(a - b));
        assert(abs_spec(b - a) == b - a);
        assert(-(a - b) == b - a);
    } else {
        assert(b - a <= 0);
        assert(abs_spec(a - b) == a - b);
        if b - a < 0 {
            assert(abs_spec(b - a) == -(b - a));
            assert(-(b - a) == a - b);
        } else {
            assert(abs_spec(b - a) == b - a);
            assert(b - a == 0);
            assert(a - b == 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    // pre-conditions-start
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    // pre-conditions-end
    // post-conditions-start
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            forall|x: int, y: int| 0 <= x && 0 <= y && x < i && y < numbers.len() && x != y ==> abs_spec(numbers[x] - numbers[y]) >= threshold
    {
        let mut j = 0;
        while j < numbers.len()
            invariant
                0 <= i < numbers.len(),
                0 <= j <= numbers.len(),
                forall|x: int, y: int| 0 <= x && 0 <= y && x < i && y < numbers.len() && x != y ==> abs_spec(numbers[x] - numbers[y]) >= threshold,
                forall|y: int| 0 <= y && y < j && i != y ==> abs_spec(numbers[i] - numbers[y]) >= threshold
        {
            if i != j {
                let diff = numbers[i] - numbers[j];
                let abs_diff = if diff < 0 { -diff } else { diff };
                if abs_diff < threshold {
                    assert(abs_spec(numbers[i] - numbers[j]) == abs_diff);
                    assert(abs_spec(numbers[i] - numbers[j]) < threshold);
                    return true;
                }
                assert(abs_spec(numbers[i] - numbers[j]) >= threshold);
            }
            j += 1;
        }
        i += 1;
    }
    
    assert(forall|x: int, y: int| 0 <= x && 0 <= y && x < numbers.len() && y < numbers.len() && x != y ==> abs_spec(numbers[x] - numbers[y]) >= threshold);
    assert(!(exists|x: int, y: int| 0 <= x && 0 <= y && x < numbers.len() && y < numbers.len() && x != y && abs_spec(numbers[x] - numbers[y]) < threshold));
    false
}
// </vc-code>

fn main() {}
}