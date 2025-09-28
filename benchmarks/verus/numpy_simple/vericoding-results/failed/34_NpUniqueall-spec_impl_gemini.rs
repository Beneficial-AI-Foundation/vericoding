// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added predicate to fix trigger issue */
spec fn is_in_arr_prefix(val: i8, arr: Seq<i8>, i: nat) -> bool {
    exists|j: int| 0 <= j < i && arr[j] == val
}

fn contains(v: &Vec<i8>, val: i8) -> (b: bool)
    ensures
        b == v@.contains(val),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            forall|k: int| 0 <= k < i ==> v@[k] != val,
        decreases v.len() - i
    {
        if v[i] == val {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
fn unique_all(arr: Vec<i8>) -> (ret: Vec<i8>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < ret@.len() && ret@[j] == #[trigger] arr@[i],
        forall|i: int, j: int| 0 <= i < ret@.len() && 0 <= j < i ==> ret@[i] != ret@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): used helper predicate to fix invariant trigger */
    let mut ret = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            ret.len() <= i,
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < ret.len() && ret@[j] == #[trigger] arr@[k],
            forall|k: int, j: int| 0 <= k < ret.len() && 0 <= j < k ==> ret@[k] != ret@[j],
            forall|k: int| 0 <= k < ret.len() ==> is_in_arr_prefix(#[trigger] ret@[k], arr@, i as nat),
        decreases arr.len() - i
    {
        let elem = arr[i];
        if !contains(&ret, elem) {
            ret.push(elem);
        }
        i = i + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}