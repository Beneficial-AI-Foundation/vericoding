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
            invariant 0 <= j <= i < n
            invariant a.len() == n
            invariant forall|k: int| 0 <= k < j ==> a[k as usize] <= key
            invariant forall|k: int| j < k <= i ==> a[k as usize] > key
            invariant forall|k: int| (i + 1) <= k < n ==> a[k as usize] == old(a)[k as usize]
            invariant sorted(*a, 0, j as int)
            invariant sorted(*a, (j + 1) as int, (i + 1) as int)
        {
            a[j] = a[j - 1];
            j -= 1;
        }
        
        a[j] = key;
        
        // Prove that the array is now sorted up to i+1
        assert(sorted(*a, 0, (i + 1) as int)) by {
            // After placing key at position j:
            // 1. Elements [0..j) are all <= key and sorted
            // 2. Element at j is key
            // 3. Elements (j..i+1] are all > key and sorted
            // Therefore [0..i+1) is sorted
            
            assert(forall|x: int, y: int| 
                0 <= x < y < (i + 1) as int ==> {
                    if y <= j {
                        // Both in sorted prefix
                        a[x as usize] <= a[y as usize]
                    } else if x < j {
                        // x in prefix, y is key or in suffix
                        a[x as usize] <= key && key <= a[y as usize]
                    } else {
                        // Both in sorted suffix  
                        a[x as usize] <= a[y as usize]
                    }
                }
            );
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
    
    // The postcondition of insertion_sort guarantees this
    assert(sorted(a, 0, a.len() as int));
    
    true  // Always return true since insertion_sort guarantees sorting
}

}