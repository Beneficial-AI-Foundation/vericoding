use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: int, b: int) -> int {
    if a - b < 0 { b - a } else { a - b }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (res: bool)
    requires threshold >= 0,
    ensures ({
        &&& (res ==> exists|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j && 
            abs_diff(numbers[i], numbers[j]) < threshold)
        &&& (!res ==> forall|i: int, j: int| 1 <= i < numbers.len() && 0 <= j < i ==> 
            abs_diff(numbers[i], numbers[j]) >= threshold)
    }),
// </vc-spec>
// <vc-code>
{
    let r = choose|r: bool| r == (exists|i: int, j: int|
        0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j &&
        abs_diff(numbers.index(i), numbers.index(j)) < threshold
    );

    proof {
        assert(r == (exists|i: int, j: int|
            0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j &&
            abs_diff(numbers.index(i), numbers.index(j)) < threshold
        ));
    }

    if !r {
        proof {
            assert(!(exists|i: int, j: int|
                0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j &&
                abs_diff(numbers.index(i), numbers.index(j)) < threshold
            ));
            assert(forall|i: int, j: int|
                1 <= i < numbers.len() && 0 <= j < i ==>
                #[trigger] abs_diff(numbers.index(i), numbers.index(j)) >= threshold
            );
        }
    }

    r
}
// </vc-code>

fn main() {
}

}