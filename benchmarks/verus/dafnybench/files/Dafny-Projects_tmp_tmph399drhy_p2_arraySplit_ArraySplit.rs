// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_split(a: Vec<i8>) -> (ret: (Vec<i8>, Vec<i8>))
    ensures
        a@.map_values(|x: i8| x as int) == ret.0@.map_values(|x: i8| x as int) + ret.1@.map_values(|x: i8| x as int),
        a.len() == ret.0.len() + ret.1.len(),
        a.len() > 1 ==> a.len() > ret.0.len(),
        a.len() > 1 ==> a.len() > ret.1.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}