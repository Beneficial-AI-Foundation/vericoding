use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_in_range(s: Seq<i32>, val: i32, start: int, end: int) -> bool {
    exists|k: int| start <= k < end && s[k] == val
}

proof fn lemma_subrange_contains(s: Seq<i32>, val: i32, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1).contains(s[i])
{
    assert(s.subrange(0, i + 1)[i] == s[i]);
}

proof fn lemma_subrange_extends(s: Seq<i32>, val: i32, i: int)
    requires 
        0 <= i < s.len(),
        s.subrange(0, i).contains(val)
    ensures s.subrange(0, i + 1).contains(val)
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    assert(forall|k: int| 0 <= k < i ==> sub_i[k] == sub_i_plus_1[k]);
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
            largest_negative.is_some() ==> arr@.subrange(0, i as int).contains(largest_negative.unwrap()) && largest_negative.unwrap() < 0,
            largest_negative.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] < 0 ==> arr@[j] <= largest_negative.unwrap(),
            smallest_positive.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            smallest_positive.is_some() ==> arr@.subrange(0, i as int).contains(smallest_positive.unwrap()) && smallest_positive.unwrap() > 0,
            smallest_positive.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] > 0 ==> arr@[j] >= smallest_positive.unwrap(),
        decreases arr.len() - i
    {
        let current = arr[i];
        
        if current < 0 {
            match largest_negative {
                None => {
                    largest_negative = Some(current);
                    proof {
                        lemma_subrange_contains(arr@, current, i as int);
                    }
                },
                Some(prev) => {
                    if current > prev {
                        largest_negative = Some(current);
                        proof {
                            lemma_subrange_contains(arr@, current, i as int);
                        }
                    } else {
                        proof {
                            lemma_subrange_extends(arr@, prev, i as int);
                        }
                    }
                }
            }
        } else if current > 0 {
            match smallest_positive {
                None => {
                    smallest_positive = Some(current);
                    proof {
                        lemma_subrange_contains(arr@, current, i as int);
                    }
                },
                Some(prev) => {
                    if current < prev {
                        smallest_positive = Some(current);
                        proof {
                            lemma_subrange_contains(arr@, current, i as int);
                        }
                    } else {
                        proof {
                            lemma_subrange_extends(arr@, prev, i as int);
                        }
                    }
                }
            }
        }
        
        i += 1;
    }
    
    (largest_negative, smallest_positive)
}
// </vc-code>

}
fn main() {}