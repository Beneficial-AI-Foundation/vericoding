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
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut largest_negative: Option<i8> = Option::None;
    let mut smallest_positive: Option<i8> = Option::None;
    
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|j: int| 0 <= j < i && arr[j] < 0 ==> 
                matches!(largest_negative, Option::Some(v)) && largest_negative->Some_0 >= arr[j],
            forall|j: int| 0 <= j < i && arr[j] > 0 ==> 
                matches!(smallest_positive, Option::Some(v)) && smallest_positive->Some_0 <= arr[j],
            matches!(largest_negative, Option::Some(_)) ==> exists|j: int| 0 <= j < i && arr[j] == largest_negative->Some_0 && arr[j] < 0,
            matches!(smallest_positive, Option::Some(_)) ==> exists|j: int| 0 <= j < i && arr[j] == smallest_positive->Some_0 && arr[j] > 0,
        decreases arr.len() - i
    {
        let val = arr[i];
        if val < 0 {
            match largest_negative {
                Option::None => {
                    largest_negative = Option::Some(val);
                },
                Option::Some(current) => {
                    if val > current {
                        largest_negative = Option::Some(val);
                    }
                }
            }
        } else if val > 0 {
            match smallest_positive {
                Option::None => {
                    smallest_positive = Option::Some(val);
                },
                Option::Some(current) => {
                    if val < current {
                        smallest_positive = Option::Some(val);
                    }
                }
            }
        }
        i = i + 1;
    }
    
    (largest_negative, smallest_positive)
}
// </vc-code>


}

fn main() {}