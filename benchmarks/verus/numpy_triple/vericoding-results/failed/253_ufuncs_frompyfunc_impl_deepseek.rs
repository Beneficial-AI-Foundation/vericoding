// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove unsupported dyn Fn trait object and use a simple wrapper function */
fn numpy_frompyfunc_helper_exec(func_wrapper: impl Fn(i8) -> i8, input: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result@[i] == func_wrapper(input@[i])
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < input.len()
        invariant
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result@[i] == func_wrapper(input@[i])
        decreases input.len() - index
    {
        let value = input[index];
        let transformed = func_wrapper(value);
        result.push(transformed);
        index = index + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc(func: spec_fn(i8) -> i8, input: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use simple closure parameter instead of trait object */
{
    let func_closure = |x: i8| -> i8 { func(x) };
    let result = numpy_frompyfunc_helper_exec(func_closure, input);
    result
}
// </vc-code>

}
fn main() {}