use vstd::prelude::*;

verus! {

//Bubblesort CS 494 submission
//References: https://stackoverflow.com/questions/69364687/how-to-prove-time-complexity-of-bubble-sort-using-dafny/69365785#69365785


// predicate checks if elements of a are in ascending order, two additional conditions are added to allow us to sort in specific range within array

spec fn sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
    recommends 
        from <= to,
        to <= a.len(),
{
    forall|x: usize, y: usize| from <= x < y < to ==> a[x as int] <= a[y as int]
}

//helps ensure swapping is valid, it is used inside the nested while loop to make sure linear order is being kept 
spec fn pivot(a: &Vec<i32>, to: usize, pvt: usize) -> bool
    recommends
        pvt < to,
        to <= a.len(),
{
    forall|x: usize, y: usize| 0 <= x < pvt < y < to ==> a[x as int] <= a[y as int] // all values within the array should be in ascending order
}

// Here having the algorithm for the bubblesort

// <vc-helpers>
// Here having the algorithm for the bubblesort

spec fn sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
    recommends 
        from <= to,
        to <= a.len(),
{
    forall|x: usize, y: usize| from <= x < y < to ==> a[x as int] <= a[y as int]
}

//helps ensure swapping is valid, it is used inside the nested while loop to make sure linear order is being kept 
spec fn pivot(a: &Vec<i32>, to: usize, pvt: usize) -> bool
    recommends
        pvt < to,
        to <= a.len(),
{
    forall|x: usize, y: usize| 0 <= x < pvt < y < to ==> a[x as int] <= a[y as int] // all values within the array should be in ascending order
}
// </vc-helpers>

// <vc-spec>
fn BubbleSort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 0, // makes sure a is not empty and length is greater than 0
    ensures 
        sorted(a, 0, a.len()), // makes sure elements of array a are sorted from 0 - a.len()
        a@.to_multiset() == old(a)@.to_multiset(), // Since a is being modified, we compare the previous elements to current elements.
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sorted(a, (a@.len() - i - 1) as usize, a@.len() as usize),
            // Note: Adjusting to handle type conversion since a@.len() is int, and sorted expects usize
            // Ensures the suffix of length i+1 is sorted, but due to loop structure, it's 0 to a.len()-i
            forall|k: usize| #![trigger sorted(a, k, a@.len() as usize)] k <= (a@.len() - i - 1) as usize ==> sorted(a, k, a@.len() as usize),
            // Better: directly use the intended suffix sorting invariant with type cast
            // Assuming the outer loop makes the last i elements sorted, so from a.len()-i to a.len()
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let mut j: usize = 0;
        while j < a.len() - 1 - i
            invariant
                0 <= j <= a.len() - 1 - i,
                forall|k: int| 0 <= k < (a@.len() as int - 1 - i as int) ==> #[trigger] (a@[k] <= a@[k + 1]),
                sorted(a, (a@.len() - i) as usize, a@.len() as usize),
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            if a[j] > a[j + 1] {
                let temp = a[j];
                a[j] = a[j + 1];
                a[j + 1] = temp;
                assert(a@[j as int] <= a@[j as int + 1]);
            }
            j += 1;
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}