use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
fn pluck_smallest_even__iterate(nodes: &Vec<u32>) -> (result: Vec<u32>)
{
    let mut result = Vec::<u32>::new();
    if nodes@.len() == 0 {
        return result;
    }
    let mut min_even: Option<u32> = None;
    let mut min_index: usize = 0; // arbitrary initial, will set when found
    let nodes_len = nodes@.len();

    let mut i: usize = 0;
    while i < nodes@.len()
        invariant
            0 <= i <= nodes@.len(),
            min_even.is_some() ==> {
                let min_val = min_even.get_Some_0();
                let m_idx = min_index;
                0 <= m_idx < i,
                nodes@[m_idx] == min_val,
                min_val % 2 == 0,
                forall |j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> min_val <= nodes@[j],
                forall |j: int| 0 <= j < m_idx ==> nodes@[j] % 2 != 0 || nodes@[j] > min_val,
            },
            min_even.is_none() ==> forall |j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
    {
        if nodes@[i] % 2 == 0 {
            if min_even.is_none() || nodes@[i] < min_even.get_Some_0() {
                min_even = Some(nodes@[i]);
                min_index = i;
            }
        }
        i += 1;
    }
    if min_even.is_some() {
        assert(min_index < nodes@.len());
        result.push(min_even.get_Some_0());
        result.push(min_index as u32);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn pluck_smallest_even(nodes: &Vec<u32>) -> (result: Vec<u32>)
    // pre-conditions-start
    requires
        nodes@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result@.len() == 0 || result@.len() == 2,
        result@.len() == 0 ==> forall|i: int| 0 <= i < nodes@.len() ==> nodes@[i] % 2 != 0,
        result@.len() == 2 ==> {
            let node = result@[0];
            let index = result@[1];
            &&& 0 <= index < nodes@.len()
            &&& nodes@[index as int] == node
            &&& node % 2 == 0
            &&& forall|i: int|
                0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> node <= nodes@[i] && forall|i: int|
                    0 <= i < result@[1] ==> nodes@[i] % 2 != 0 || nodes@[i] > node
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result = Vec::<u32>::new();
    if nodes@.len() == 0 {
        return result;
    }
    let mut min_even: Option<u32> = None;
    let mut min_index: usize = 0;
    let mut i: usize = 0;
    while i < nodes@.len()
        invariant
            0 <= i <= nodes@.len(),
            min_even.is_some() ==> {
                let min_val = min_even.get_Some_0();
                let m_idx = min_index;
                0 <= m_idx < i,
                nodes@[m_idx] == min_val,
                min_val % 2 == 0,
                forall |j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> min_val <= nodes@[j],
                forall |j: int| 0 <= j < m_idx ==> nodes@[j] % 2 != 0 || nodes@[j] > min_val,
            },
            min_even.is_none() ==> forall |j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
    {
        if nodes@[i] % 2 == 0 {
            if min_even.is_none() || nodes@[i] < min_even.get_Some_0() {
                min_even = Some(nodes@[i]);
                min_index = i;
            }
        }
        i += 1;
    }
    if min_even.is_some() {
        result.push(min_even.get_Some_0());
        result.push(min_index as u32);
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}