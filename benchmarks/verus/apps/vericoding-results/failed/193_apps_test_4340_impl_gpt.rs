// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn transform_element(x: int) -> int {
    if x % 2 == 0 { x - 1 } else { x }
}

spec fn valid_transformation(input: Seq<int>, output: Seq<int>) -> bool {
    output.len() == input.len() &&
    forall|i: int| 0 <= i < input.len() ==> output[i] == transform_element(input[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): parity characterization of transform_element and cast subtraction lemma */
proof fn lemma_cast_sub_i8_preserves(x: i8)
    requires
        x > i8::MIN,
    ensures
        (x - 1) as int == (x as int) - 1,
{
    assert((x - 1) as int == (x as int) - (1i8 as int));
    assert(1i8 as int == 1);
}

/* helper modified by LLM (iteration 5): relate transform_element to parity explicitly */
proof fn lemma_transform_matches_parity(x: int)
    ensures
        (x % 2 == 0) ==> transform_element(x) == x - 1,
        (x % 2 != 0) ==> transform_element(x) == x,
{
    if x % 2 == 0 {
        assert(transform_element(x) == x - 1);
    } else {
        assert(transform_element(x) == x);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: Vec<i8>)
    ensures valid_transformation(a@.map(|_i, x| x as int), result@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use i8 parity in executable code to avoid 'int' in exec context */
    let n = a.len();
    let mut i: usize = 0;
    let mut result: Vec<i8> = Vec::new();
    while i < n
        invariant
            i <= n,
            n == a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] ((result@[j]) as int) == transform_element((a@[j]) as int),
        decreases (n - i) as int
    {
        let xi: i8 = a[i];
        let yi: i8;
        if xi % 2 == 0i8 {
            if xi > i8::MIN {
                yi = xi - 1;
                proof {
                    lemma_cast_sub_i8_preserves(xi);
                    lemma_transform_matches_parity(xi as int);
                    assert((yi as int) == (xi as int) - 1);
                }
            } else {
                yi = xi;
                proof {
                    lemma_transform_matches_parity(xi as int);
                }
            }
        } else {
            yi = xi;
            proof {
                lemma_transform_matches_parity(xi as int);
                assert((yi as int) == (xi as int));
            }
        }
        result.push(yi);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}