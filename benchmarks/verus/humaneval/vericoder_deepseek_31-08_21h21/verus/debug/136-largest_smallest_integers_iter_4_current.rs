use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_negative(x: i32) -> bool {
    x < 0
}

spec fn is_positive(x: i32) -> bool {
    x > 0
}

proof fn find_negative_max_proof(arr: Seq<i32>, i: int, current_max: i32) 
    requires
        0 <= i <= arr.len(),
        is_negative(current_max),
    ensures
        forall|j: int| 0 <= j < i && is_negative(arr[j]) ==> arr[j] <= current_max
    decreases i
{
    if i > 0 {
        find_negative_max_proof(arr, i - 1, current_max);
    }
}

proof fn find_positive_min_proof(arr: Seq<i32>, i: int, current_min: i32) 
    requires
        0 <= i <= arr.len(),
        is_positive(current_min),
    ensures
        forall|j: int| 0 <= j < i && is_positive(arr[j]) ==> arr[j] >= current_min
    decreases i
{
    if i > 0 {
        find_positive_min_proof(arr, i - 1, current_min);
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
    let mut neg_max: Option<i32> = None;
    let mut pos_min: Option<i32> = None;
    
    let mut idx: usize = 0;
    while idx < arr.len()
        invariant
            idx <= arr@.len(),
            neg_max.is_none() ==> forall|i: int| 0 <= i < idx ==> arr@[i] >= 0,
            neg_max.is_some() ==> {
                let max_val = neg_max.unwrap();
                arr@.contains(max_val) && max_val < 0
                && forall|i: int| 0 <= i < idx && arr@[i] < 0 ==> arr@[i] <= max_val
            },
            pos_min.is_none() ==> forall|i: int| 0 <= i < idx ==> arr@[i] <= 0,
            pos_min.is_some() ==> {
                let min_val = pos_min.unwrap();
                arr@.contains(min_val) && min_val > 0
                && forall|i: int| 0 <= i < idx && arr@[i] > 0 ==> arr@[i] >= min_val
            }
        decreases arr.len() - idx
    {
        let elem = arr[idx];
        
        if elem < 0 {
            match neg_max {
                Some(current_max) => {
                    if elem > current_max {
                        neg_max = Some(elem);
                        proof {
                            find_negative_max_proof(arr@, idx as int, elem);
                        }
                    } else {
                        proof {
                            find_negative_max_proof(arr@, idx as int, current_max);
                        }
                    }
                }
                None => {
                    neg_max = Some(elem);
                    proof {
                        find_negative_max_proof(arr@, idx as int, elem);
                    }
                }
            }
        } else if neg_max.is_some() {
            proof {
                find_negative_max_proof(arr@, (idx + 1) as int, neg_max.unwrap());
            }
        }
        
        if elem > 0 {
            match pos_min {
                Some(current_min) => {
                    if elem < current_min {
                        pos_min = Some(elem);
                        proof {
                            find_positive_min_proof(arr@, idx as int, elem);
                        }
                    } else {
                        proof {
                            find_positive_min_proof(arr@, idx as int, current_min);
                        }
                    }
                }
                None => {
                    pos_min = Some(elem);
                    proof {
                        find_positive_min_proof(arr@, idx as int, elem);
                    }
                }
            }
        } else if pos_min.is_some() {
            proof {
                find_positive_min_proof(arr@, (idx + 1) as int, pos_min.unwrap());
            }
        }
        
        idx += 1;
    }
    
    (neg_max, pos_min)
}
// </vc-code>

fn main() {}
}