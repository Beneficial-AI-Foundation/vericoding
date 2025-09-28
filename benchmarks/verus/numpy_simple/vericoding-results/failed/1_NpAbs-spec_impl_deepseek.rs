// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_int(x: int) -> int {
    if x < 0 { -x } else { x }
}
// </vc-preamble>

// <vc-helpers>

spec fn abs_int_helper(x: i8) -> i8
    ensures
        result as int == abs_int(x as int),
        result >= 0,
{
    if x < 0 {
        (-(x as int)) as i8
    } else {
        x
    }
}

proof fn abs_vec_lemma(a: Seq<i8>, i: int)
    requires
        0 <= i <= a.len(),
    ensures
        forall|j: int| i <= j < a.len() ==> abs_int_helper(a[j]) as int == abs_int(a[j] as int) && abs_int_helper(a[j]) >= 0,
{
    assert forall|j: int| i <= j < a.len() implies abs_int_helper(a[j]) as int == abs_int(a[j] as int) && abs_int_helper(a[j]) >= 0 by {
        if a[j] < 0 {
            assert(-(a[j] as int) == abs_int(a[j] as int));
        } else {
            assert(a[j] as int == abs_int(a[j] as int));
        }
    };
}

// </vc-helpers>

// <vc-spec>
fn abs(a: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == abs_int(a[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type conversion with ghost wrapper */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> result@[j] as int == abs_int(a@[j] as int),
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
        decreases a.len() - i,
    {
        proof { abs_vec_lemma(a@, i); }
        let element = a[i];
        let abs_val = ghost_closure!{
            |element: i8| -> i8 {
                if element < 0 {
                    (-(element as int)) as i8
                } else {
                    element
                }
            }
        }(element);
        result.push(abs_val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}