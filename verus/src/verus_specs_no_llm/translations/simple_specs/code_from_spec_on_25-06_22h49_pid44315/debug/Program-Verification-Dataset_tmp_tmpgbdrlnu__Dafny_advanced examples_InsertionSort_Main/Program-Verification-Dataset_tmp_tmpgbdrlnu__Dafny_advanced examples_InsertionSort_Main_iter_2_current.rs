use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    let mut a = vec![3, 2, 5, 1, 8];
    insertion_sort(&mut a);
    println!("{:?}", a);
}

spec fn sorted(a: Vec<int>, start: int, end: int) -> bool
    requires 0 <= start <= end <= a.len()
{
    forall|j: int, k: int| start <= j < k < end ==> a[j as usize] <= a[k as usize]
}

fn insertion_sort(a: &mut Vec<int>)
    ensures sorted(*a, 0, a.len() as int)
    ensures a.len() == old(a).len()
{
    let n = a.len();
    let mut i = 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant a.len() == n
        invariant sorted(*a, 0, i as int)
    {
        let key = a[i];
        let mut j = i;
        
        while j > 0 && a[j - 1] > key
            invariant j <= i
            invariant a.len() == n
            invariant forall|k: int| 0 <= k < j ==> a[k as usize] <= key
            invariant forall|k: int| j < k <= i ==> a[k as usize] > key
            invariant sorted(*a, 0, j as int)
            invariant sorted(*a, j as int + 1, i as int + 1)
        {
            a[j] = a[j - 1];
            j -= 1;
        }
        
        a[j] = key;
        
        // Proof assertion to help verification
        assert(sorted(*a, 0, (i + 1) as int));
        
        i += 1;
    }
}

// Test function
fn test_main() -> (result: bool)
    ensures result == true
{
    let mut a = vec![3, 2, 5, 1, 8];
    insertion_sort(&mut a);
    
    // Verify the array is sorted
    let sorted_correctly = a[0] <= a[1] && a[1] <= a[2] && a[2] <= a[3] && a[3] <= a[4];
    
    // Proof assertion
    assert(sorted(a, 0, a.len() as int));
    
    sorted_correctly
}

}