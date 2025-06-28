use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    let _ = Main();
}

spec fn acheck(a: Vec<int>, n: int) -> bool
{
    n >= 1 &&
    a.len() % 2 == 0 && 
    forall|i: int| 0 <= i < a.len() ==> 
        if i % n == 0 { a[i] == 0 } else { a[i] != 0 }
}

// Executable version of acheck
fn acheck_exec(a: &Vec<i32>, n: i32) -> (result: bool)
    requires n >= 1
    ensures result == acheck(a@.map(|_, x: i32| x as int), n as int)
{
    if a.len() % 2 != 0 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            n >= 1,
            a.len() % 2 == 0,
            forall|j: int| 0 <= j < i ==> 
                if j % (n as int) == 0 { a@[j] as int == 0 } else { a@[j] as int != 0 }
    {
        let i_int = i as int;
        let n_int = n as int;
        
        // Check if i is divisible by n
        let is_divisible = (i_int % n_int) == 0;
        
        if is_divisible {
            if a[i] != 0 {
                proof {
                    // Prove that the condition fails for index i
                    assert(i_int % n_int == 0);
                    assert(a@[i_int] as int != 0);
                    assert(!acheck(a@.map(|_, x: i32| x as int), n as int));
                }
                return false;
            }
        } else {
            if a[i] == 0 {
                proof {
                    // Prove that the condition fails for index i
                    assert(i_int % n_int != 0);
                    assert(a@[i_int] as int == 0);
                    assert(!acheck(a@.map(|_, x: i32| x as int), n as int));
                }
                return false;
            }
        }
        i += 1;
    }
    
    proof {
        // Prove that all conditions are satisfied
        let mapped_a = a@.map(|_, x: i32| x as int);
        assert(n as int >= 1);
        assert(mapped_a.len() % 2 == 0);
        assert(forall|j: int| 0 <= j < mapped_a.len() ==> 
            if j % (n as int) == 0 { mapped_a[j] == 0 } else { mapped_a[j] != 0 });
        assert(acheck(mapped_a, n as int));
    }
    
    true
}

fn Main() -> (result: bool)
{
    // Test case 1: [0, 42, 0, 42] with n=2
    let mut arr1: Vec<i32> = Vec::new();
    arr1.push(0);
    arr1.push(42);
    arr1.push(0);
    arr1.push(42);
    let res1 = acheck_exec(&arr1, 2);
    
    // Test case 2: empty array with n=2
    let arr2: Vec<i32> = Vec::new();
    let res2 = acheck_exec(&arr2, 2);
    
    // Test case 3: [0, 4, 2, 0] with n=2
    let mut arr3: Vec<i32> = Vec::new();
    arr3.push(0);
    arr3.push(4);
    arr3.push(2);
    arr3.push(0);
    let res3 = acheck_exec(&arr3, 2);
    
    // Return the combination of results
    res1 && res2 && res3
}

}