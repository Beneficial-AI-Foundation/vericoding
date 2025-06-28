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
    ensures a@.to_multiset() == old(a)@.to_multiset()
{
    let n = a.len();
    let mut i = 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant a.len() == n
        invariant sorted(*a, 0, i as int)
        invariant a@.to_multiset() == old(a)@.to_multiset()
    {
        let key = a[i];
        let mut j = i;
        
        // Store the original array state before inner modifications
        let ghost original_a = *a;
        
        // Shift elements to the right until we find the correct position
        while j > 0 && a[j - 1] > key
            invariant 0 <= j <= i < n
            invariant a.len() == n
            invariant key == original_a[i as usize]
            invariant forall|k: int| 0 <= k < j ==> a[k as usize] == original_a[k as usize]
            invariant forall|k: int| j < k <= i ==> a[k as usize] == original_a[(k - 1) as usize]
            invariant forall|k: int| (i + 1) <= k < n ==> a[k as usize] == original_a[k as usize]
            invariant sorted(*a, 0, j as int)
            invariant forall|k: int| j < k <= i ==> a[k as usize] > key
            invariant a@.to_multiset() == original_a@.to_multiset()
        {
            a[j] = a[j - 1];
            j -= 1;
        }
        
        // Insert the key at the correct position
        a[j] = key;
        
        // Prove properties after insertion
        assert(forall|k: int| 0 <= k < j ==> a[k as usize] <= key) by {
            if j > 0 {
                assert(a[j - 1] <= key);
                assert(sorted(*a, 0, j as int));
            }
        };
        
        assert(forall|k: int| j < k <= i ==> key <= a[k as usize]) by {
            assert(forall|k: int| j < k <= i ==> a[k as usize] > key);
        };
        
        // Prove that the range [0, i+1) is now sorted
        assert(sorted(*a, 0, (i + 1) as int)) by {
            assert(forall|x: int, y: int| 0 <= x < y <= i ==> {
                if x < j && y == j {
                    a[x as usize] <= key
                } else if x == j && y > j {
                    key <= a[y as usize]
                } else if x < j && y > j {
                    // transitivity: a[x] <= key <= a[y]
                    a[x as usize] <= a[y as usize]
                } else {
                    // both in same sorted region
                    a[x as usize] <= a[y as usize]
                }
            });
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
    
    // The postcondition of insertion_sort guarantees this
    assert(sorted(a, 0, a.len() as int));
    
    true
}

}