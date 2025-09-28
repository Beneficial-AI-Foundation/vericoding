// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn get_value(o: Option<int>) -> int
    recommends o.is_Some()
{
    o.get_Some_0()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: Vec<i8>) -> (result: (Option<i8>, Option<i8>))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    if arr.len() == 0 {
        return (Option::None, Option::None);
    }
    
    let mut largest = arr[0];
    let mut smallest = arr[0];
    let mut i = 1;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            largest >= smallest,
            forall|j: int| 0 <= j < i ==> arr@[j] <= largest,
            forall|j: int| 0 <= j < i ==> arr@[j] >= smallest,
            exists|j: int| 0 <= j < i && arr@[j] == largest,
            exists|j: int| 0 <= j < i && arr@[j] == smallest,
        decreases arr.len() - i
    {
        if arr[i] > largest {
            largest = arr[i];
        }
        if arr[i] < smallest {
            smallest = arr[i];
        }
        i += 1;
    }
    
    (Option::Some(largest), Option::Some(smallest))
}
// </vc-code>


}

fn main() {}