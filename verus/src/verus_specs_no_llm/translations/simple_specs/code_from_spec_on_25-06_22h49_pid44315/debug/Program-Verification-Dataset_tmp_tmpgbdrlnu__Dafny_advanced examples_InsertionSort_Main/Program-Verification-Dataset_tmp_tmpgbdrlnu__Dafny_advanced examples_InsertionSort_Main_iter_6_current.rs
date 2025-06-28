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
        
        // Shift elements to the right until we find the correct position
        while j > 0 && a[j - 1] > key
            invariant 0 <= j <= i < n
            invariant a.len() == n
            invariant forall|k: int| 0 <= k < j ==> a[k as usize] <= key
            invariant forall|k: int| j < k <= i ==> a[k as usize] > key
        {
            a[j] = a[j - 1];
            j -= 1;
        }
        
        // Insert the key at the correct position
        a[j] = key;
        
        // At this point, we need to prove that a[0..i+1] is sorted
        // The key insight is that:
        // - a[0..j] contains elements <= key and is sorted
        // - a[j] = key  
        // - a[j+1..i+1] contains elements > key and is sorted
        // Therefore a[0..i+1] is sorted
        
        assert(sorted(*a, 0, (i + 1) as int)) by {
            // For any two indices x, y where 0 <= x < y < i+1
            assert(forall|x: int, y: int| 
                0 <= x < y < (i + 1) as int ==> {
                    let x_val = a[x as usize];
                    let y_val = a[y as usize];
                    if y < j {
                        // Both in the left sorted part
                        x_val <= y_val  // from sorted(a, 0, j)
                    } else if x < j && y == j {
                        // x in left part, y is the key position
                        x_val <= key  // from invariant
                    } else if x < j && y > j {
                        // x in left part, y in right part
                        x_val <= key && key < y_val  // from invariants
                    } else if x == j && y > j {
                        // x is key, y in right part
                        key < y_val  // from invariant
                    } else {
                        // Both in right sorted part
                        x_val <= y_val  // from sorted property of shifted elements
                    }
                }
            );
        }
        
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
    
    true  // Always return true since insertion_sort guarantees sorting
}

}