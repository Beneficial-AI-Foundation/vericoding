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
        
        while j > 0 && a[j - 1] > key
            invariant j <= i
            invariant a.len() == n
            invariant key == old(a)[i]
            invariant forall|k: int| 0 <= k < j ==> a[k as usize] <= key
            invariant forall|k: int| j < k <= i ==> a[k as usize] > key
            invariant forall|k: int| j < k <= i ==> a[k as usize] == old(a)[(k-1) as usize]
            invariant sorted(*a, 0, j as int)
            invariant sorted(*a, j as int + 1, i as int + 1)
            invariant forall|k: int| 0 <= k < j && j + 1 <= k <= i ==> a[k as usize] <= a[(k) as usize]
        {
            a[j] = a[j - 1];
            j -= 1;
        }
        
        a[j] = key;
        
        // Prove that inserting the key maintains sortedness
        assert(forall|k: int| 0 <= k < j ==> a[k as usize] <= key);
        assert(forall|k: int| j < k <= i ==> key <= a[k as usize]);
        assert(sorted(*a, 0, j as int));
        assert(sorted(*a, j as int + 1, i as int + 1));
        
        // Key insight: prove the connection between segments
        if j > 0 {
            assert(a[(j-1) as usize] <= key);
        }
        if j < i {
            assert(key <= a[(j+1) as usize]);
        }
        
        // Now we can prove the entire prefix is sorted
        assert(sorted(*a, 0, (i + 1) as int)) by {
            // The proof follows from the fact that:
            // 1. [0..j) is sorted and all elements <= key
            // 2. key is at position j
            // 3. (j..i+1] is sorted and all elements >= key
        };
        
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