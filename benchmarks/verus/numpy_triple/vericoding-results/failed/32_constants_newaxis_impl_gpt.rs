// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum NewAxis {
    Newaxis,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): robust single-element Vec constructor for generic T without cloning */
fn singleton_vec<T>(x: T) -> (res: Vec<T>)
    ensures
        res.len() == 1,
        res[0] == x
{
    let mut v: Vec<T> = Vec::new();
    v.push(x);
    v
}
// </vc-helpers>

// <vc-spec>
fn expand_to_column<T>(v: Vec<T>, axis: NewAxis) -> (result: Vec<Vec<T>>)
    ensures
        result.len() == v.len(),
        forall|i: int| 0 <= i < result.len() ==> (
            result[i].len() == 1 &&
            result[i][0] == v[i]
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): removed bound-only quantifiers and added int casts to fix trigger inference */
    let ghost snap = v@;
    let n_usize = v.len();
    let ghost n: int = n_usize as int;
    let _axis = axis;

    let mut v_mut = v;
    let mut rev: Vec<Vec<T>> = Vec::new();

    while v_mut.len() > 0
        invariant
            v_mut.len() + rev.len() == n_usize,
            forall|j:int| 0 <= j < v_mut.len() as int ==> v_mut@[j] == snap[j],
            forall|k:int|
                0 <= k < rev.len() as int ==> (
                    0 <= n - 1 - k < n &&
                    rev[k].len() == 1 &&
                    rev[k][0] == snap[n - 1 - k]
                )
        decreases v_mut.len()
    {
        match v_mut.pop() {
            Option::Some(elem) => {
                let inner = singleton_vec(elem);
                rev.push(inner);
            }
            Option::None => { }
        }
    }

    let mut res: Vec<Vec<T>> = Vec::new();

    while rev.len() > 0
        invariant
            res.len() + rev.len() == n_usize,
            forall|k:int|
                0 <= k < res.len() as int ==> (
                    k < n &&
                    res[k].len() == 1 &&
                    res[k][0] == snap[k]
                ),
            forall|k:int|
                0 <= k < rev.len() as int ==> (
                    0 <= n - 1 - k < n &&
                    rev[k].len() == 1 &&
                    rev[k][0] == snap[n - 1 - k]
                )
        decreases rev.len()
    {
        match rev.pop() {
            Option::Some(inner) => {
                res.push(inner);
            }
            Option::None => { }
        }
    }

    res
}
// </vc-code>

}
fn main() {}