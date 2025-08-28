use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_value_in_range(arr: Seq<i32>, start: int, end: int, val: i32) -> bool {
    exists|k: int| start <= k < end && arr[k] == val
}

proof fn lemma_subrange_contains_equiv(arr: Seq<i32>, end: int, val: i32)
    requires 0 <= end <= arr.len()
    ensures arr.subrange(0, end).contains(val) <==> contains_value_in_range(arr, 0, end, val)
{
    if arr.subrange(0, end).contains(val) {
        let sub = arr.subrange(0, end);
        assert(exists|k: int| 0 <= k < sub.len() && sub[k] == val);
    }
    if contains_value_in_range(arr, 0, end, val) {
        let k = choose|k: int| 0 <= k < end && arr[k] == val;
        assert(arr.subrange(0, end)[k] == val);
    }
}
// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: &Vec<i32>) -> (res: (Option<i32>, Option<i32>))
    // post-conditions-start
    ensures
        ({
            let a = res.0;
            let b = res.1;
            &&& a.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] >= 0
            &&& a.is_some() ==> arr@.contains(a.unwrap()) && a.unwrap() < 0
            &&& a.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] < 0 ==> arr@[i] <= a.unwrap()
            &&& b.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] <= 0
            &&& b.is_some() ==> arr@.contains(b.unwrap()) && b.unwrap() > 0
            &&& b.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] > 0 ==> arr@[i] >= b.unwrap()
        }),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut largest_negative: Option<i32> = None;
    let mut smallest_positive: Option<i32> = None;
    
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            largest_negative.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] >= 0,
            largest_negative.is_some() ==> contains_value_in_range(arr@, 0, i as int, largest_negative.unwrap()) && largest_negative.unwrap() < 0,
            largest_negative.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] < 0 ==> arr@[j] <= largest_negative.unwrap(),
            smallest_positive.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            smallest_positive.is_some() ==> contains_value_in_range(arr@, 0, i as int, smallest_positive.unwrap()) && smallest_positive.unwrap() > 0,
            smallest_positive.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] > 0 ==> arr@[j] >= smallest_positive.unwrap()
        decreases arr.len() - i
    {
        let val = arr[i];
        
        if val < 0 {
            if largest_negative.is_none() || val > largest_negative.unwrap() {
                largest_negative = Some(val);
            }
        } else if val > 0 {
            if smallest_positive.is_none() || val < smallest_positive.unwrap() {
                smallest_positive = Some(val);
            }
        }
        
        i += 1;
    }
    
    proof {
        if largest_negative.is_some() {
            lemma_subrange_contains_equiv(arr@, arr.len() as int, largest_negative.unwrap());
        }
        if smallest_positive.is_some() {
            lemma_subrange_contains_equiv(arr@, arr.len() as int, smallest_positive.unwrap());
        }
    }
    
    (largest_negative, smallest_positive)
}
// </vc-code>

}
fn main() {}