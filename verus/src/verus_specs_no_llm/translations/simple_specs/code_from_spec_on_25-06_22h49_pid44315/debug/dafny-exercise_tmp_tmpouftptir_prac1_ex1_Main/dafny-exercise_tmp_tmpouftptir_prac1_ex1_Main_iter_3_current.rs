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
            forall|j: int| 0 <= j < i ==> 
                if j % (n as int) == 0 { a@[j] as int == 0 } else { a@[j] as int != 0 }
    {
        if (i as i32) % n == 0 {
            if a[i] != 0 {
                return false;
            }
        } else {
            if a[i] == 0 {
                return false;
            }
        }
        i += 1;
    }
    true
}

fn Main() -> (result: bool)
{
    let arr1: Vec<i32> = Vec::new();
    arr1.push(0);
    arr1.push(42);
    arr1.push(0);
    arr1.push(42);
    let res1 = acheck_exec(&arr1, 2);
    
    let arr2: Vec<i32> = Vec::new();
    let res2 = acheck_exec(&arr2, 2);
    
    let arr3: Vec<i32> = Vec::new();
    arr3.push(0);
    arr3.push(4);
    arr3.push(2);
    arr3.push(0);
    let res3 = acheck_exec(&arr3, 2);
    
    // Return the combination of results
    res1 && res2 && res3
}

}