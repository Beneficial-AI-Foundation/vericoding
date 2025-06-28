use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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
        
        if i % (n as usize) == 0 {
            if a[i] != 0 {
                proof {
                    assert(a@[i_int] as int != 0);
                    assert(i_int % n_int == 0);
                    assert(!(if i_int % n_int == 0 { a@[i_int] == 0 } else { a@[i_int] != 0 }));
                }
                return false;
            }
        } else {
            if a[i] == 0 {
                proof {
                    assert(a@[i_int] as int == 0);
                    assert(i_int % n_int != 0);
                    assert(!(if i_int % n_int == 0 { a@[i_int] == 0 } else { a@[i_int] != 0 }));
                }
                return false;
            }
        }
        i += 1;
    }
    
    proof {
        let a_spec = a@.map(|_, x: i32| x as int);
        assert(a_spec.len() == a@.len());
        assert(forall|j: int| 0 <= j < a@.len() ==> a_spec[j] == a@[j] as int);
        assert(forall|j: int| 0 <= j < a_spec.len() ==> 
            if j % (n as int) == 0 { a_spec[j] == 0 } else { a_spec[j] != 0 });
        assert(acheck(a_spec, n as int));
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