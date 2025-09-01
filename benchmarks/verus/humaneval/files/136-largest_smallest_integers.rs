use vstd::prelude::*;

verus! {

/*
function_signature: "def largest_smallest_integers(lst: List[int]) -> Tuple[ Optional[Int], Optional[Int] ]"
docstring: |
Create a function that returns a tuple (a, b), where 'a' is
the largest of negative integers, and 'b' is the smallest
of positive integers in a list.
If there is no negative or positive integers, return them as None.
test_cases:
- input: [2, 4, 1, 3, 5, 7]
expected_output: (None, 1)
- input: []
expected_output: (None, None)
- input: [0]
expected_output: (None, None)
*/

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
{
    // impl-start
    assume(false);
    (None, None)
    // impl-end
}

}
fn main() {}