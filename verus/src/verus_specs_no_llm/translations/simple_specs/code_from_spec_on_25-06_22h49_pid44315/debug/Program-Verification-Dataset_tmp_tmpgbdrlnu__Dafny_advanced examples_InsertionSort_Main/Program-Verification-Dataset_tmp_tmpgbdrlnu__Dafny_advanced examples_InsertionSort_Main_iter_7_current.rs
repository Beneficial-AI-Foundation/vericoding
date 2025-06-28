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

spec fn sorted_up_to(a: Vec<int>, end: int) -> bool
    requires 0 <= end <= a.len()
{
    forall|j: int, k: int| 0 <= j < k < end ==> a[j as usize] <= a[k as usize]
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
        
        // Store the original array for proof purposes
        proof {
            let ghost orig_a = *a;
        }
        
        // Shift elements to the right until we find the correct position
        while j > 0 && a[j - 1] > key
            invariant 0 <= j <= i < n
            invariant a.len() == n
            invariant key == old(a)[i]
            invariant sorted(*a, 0, j as int)
            invariant forall|k: int| j < k <= i ==> a[k as usize] > key
            invariant forall|k: int| (j < k <= i) ==> (a[k as usize] == old(a)[(k-1) as usize])
        {
            a[j] = a[j - 1];
            j -= 1;
        }
        
        // Insert the key at the correct position
        a[j] = key;
        
        // Prove that the array is sorted up to i+1
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
    
    // The postcondition of insertion_sort guarantees this
    assert(sorted(a, 0, a.len() as int));
    
    true
}

}