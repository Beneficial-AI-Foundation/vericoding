use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
fn pluck_smallest_even__iterate(nodes: &Vec<u32>) -> (result: Vec<u32>)
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
              0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> node <= nodes@[i]
      },
{
    let mut result = Vec::<u32>::new();
    if nodes@.len() == 0nat {
        return result;
    }
    let mut min_even: Option<u32> = None;
    let mut min_index: usize = 0;
    let mut i: usize = 0;
    while i < nodes@.len() as usize
        invariant
            0 <= i <= nodes@.len() as usize,
            min_even.is_some() ==> {
                0 <= min_index < i;
                nodes@[min_index as int] == min_even.get();
                min_even.get() % 2 == 0;
                forall |j: int| 0 <= j < i as int && nodes@[j] % 2 == 0 ==> min_even.get() <= nodes@[j];
                forall |j: int| 0 <= j < min_index as int ==> nodes@[j] % 2 != 0 || nodes@[j] > min_even.get();
            },
            min_even.is_none() ==> forall |j: int| 0 <= j < i as int ==> nodes@[j] % 2 != 0,
    {
        if nodes@[i as int] % 2 == 0 {
            if min_even.is_none() || nodes@[i as int] < min_even.get() {
                min_even = Some(nodes@[i as int]);
                min_index = i;
            }
        }
        i += 1;
    }
    if min_even.is_some() {
        result.push(min_even.get());
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
    let mut result = Vec::<u32>::new();
    if nodes@.len() == 0nat {
        return result;
    }
    let mut min_even: Option<u32> = None;
    let mut min_index: usize = 0;
    let mut i: usize = 0;
    while i < nodes@.len() as usize
        invariant
            0 <= i <= nodes@.len() as usize,
            min_even.is_some() ==> {
                0 <= min_index < i;
                nodes@[min_index as int] == min_even.get();
                min_even.get() % 2 == 0;
                forall |j: int| 0 <= j < i as int && nodes@[j] % 2 == 0 ==> min_even.get() <= nodes@[j];
                forall |j: int| 0 <= j < min_index as int ==> nodes@[j] % 2 != 0 || nodes@[j] > min_even.get();
            },
            min_even.is_none() ==> forall |j: int| 0 <= j < i as int ==> nodes@[j] % 2 != 0,
    {
        if nodes@[i as int] % 2 == 0 {
            if min_even.is_none() || nodes@[i as int] < min_even.get() {
                min_even = Some(nodes@[i as int]);
                min_index = i;
            }
        }
        i += 1;
    }
    if min_even.is_some() {
        result.push(min_even.get());
        result.push(min_index as u32);
    }
    result
}
// </vc-code>

fn main() {}
}