// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn same_len_return_first<T>(a: Vec<T>, b: Vec<T>) -> (res: Vec<T>)
    requires
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
{
    a
}
// </vc-helpers>

// <vc-spec>
fn mod_func(a: Vec<String>, values: Vec<String>) -> (result: Vec<String>)
    requires a.len() == values.len(),
    ensures 
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    let r = same_len_return_first(a, values);
    r
}
// </vc-code>

}
fn main() {}