// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn compute_max_len(c1: &Vec<i8>, c2: &Vec<i8>) -> (max_len: usize)
    ensures
        max_len as int >= c1@.len(),
        max_len as int >= c2@.len(),
        max_len as int == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() }
{
    if c1.len() >= c2.len() {
        c1.len()
    } else {
        c2.len()
    }
}

fn get_element(vec: &Vec<i8>, i: usize) -> (val: i8)
    requires
        i < vec@.len()
    ensures
        val == vec@[i as int]
{
    vec[i]
}

spec fn get_element_spec(vec: Seq<i8>, i: int) -> int
{
    if 0 <= i < vec.len() {
        vec[i] as int
    } else {
        0
    }
} /* helper modified by LLM (iteration 5): fixed requires condition in get_element */
// </vc-helpers>

// <vc-spec>
fn legadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let val1: int = if i < c1@.len() { c1@[i] as int } else { 0 };
            let val2: int = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == val1 + val2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant indexing */
    let max_len = compute_max_len(&c1, &c2);
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < max_len
        invariant
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> {
                let val1 = if j < c1@.len() { c1@[j] as int } else { 0 };
                let val2 = if j < c2@.len() { c2@[j] as int } else { 0 };
                #[trigger] result@[j] as int == val1 + val2
            },
        decreases max_len - i
    {
        let val1 = if i < c1.len() { c1[i] } else { 0 };
        let val2 = if i < c2.len() { c2[i] } else { 0 };
        let sum = (val1 as int + val2 as int) as i8;
        result.push(sum);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}