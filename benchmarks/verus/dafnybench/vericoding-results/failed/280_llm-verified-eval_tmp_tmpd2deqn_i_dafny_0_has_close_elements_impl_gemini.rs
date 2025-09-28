// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added exec_abs for use in exec code */
fn exec_abs(x: int) -> (res: int)
    ensures res == abs(x)
{
    if x < 0 { -x } else { x }
}

/* helper modified by LLM (iteration 2): fixed compilation error by implementing helper lemmas for abs */
proof fn lemma_abs_is_symmetric(x: int)
    ensures abs(-x) == abs(x)
{
}

proof fn lemma_abs_sub_commutes(a: int, b: int)
    ensures abs(a - b) == abs(b - a)
{
    lemma_abs_is_symmetric(a - b);
}

proof fn lemma_no_close_pairs_from_ordered(numbers: Seq<int>, threshold: int)
    requires
        forall|i: int, j: int|
            0 <= i < numbers.len() &&
            i < j < numbers.len() ==> 
            abs(numbers[i] - numbers[j]) >= threshold,
    ensures
        !exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold,
{
    assert forall|i: int, j: int|
        0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j implies
        abs(numbers[i] - numbers[j]) >= threshold
    by {
        if i < j {
            // holds by requires
        } else {
            assert(j < i);
            lemma_abs_sub_commutes(numbers[i], numbers[j]);
            assert(abs(numbers[j] - numbers[i]) >= threshold);
        }
    };
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
    /* code modified by LLM (iteration 3): fixed compilation errors by casting types and using spec indexing */
    let mut i: int = 0 as int;
    while i < numbers.len() as int
        invariant
            0 <= i <= numbers.len() as int,
            forall|x: int, y: int| 0 <= x < i && x < y < numbers.len() as int ==> abs(numbers@[x] - numbers@[y]) >= threshold,
            numbers.len() == old(numbers).len(),
            threshold == old(threshold)
        decreases (numbers.len() as int) - i
    {
        let mut j: int = i + (1 as int);
        while j < numbers.len() as int
            invariant
                0 <= i < numbers.len() as int,
                i < j <= numbers.len() as int,
                forall|y: int| i < y < j ==> abs(numbers@[i] - numbers@[y]) >= threshold,
                forall|x: int, y: int| 0 <= x < i && x < y < numbers.len() as int ==> abs(numbers@[x] - numbers@[y]) >= threshold,
                numbers.len() == old(numbers).len(),
                threshold == old(threshold)
            decreases (numbers.len() as int) - j
        {
            if exec_abs(numbers@[i] - numbers@[j]) < threshold {
                return true;
            }
            j = j + (1 as int);
        }
        i = i + (1 as int);
    }

    lemma_no_close_pairs_from_ordered(numbers, threshold);
    return false;
}
// </vc-code>

}
fn main() {}