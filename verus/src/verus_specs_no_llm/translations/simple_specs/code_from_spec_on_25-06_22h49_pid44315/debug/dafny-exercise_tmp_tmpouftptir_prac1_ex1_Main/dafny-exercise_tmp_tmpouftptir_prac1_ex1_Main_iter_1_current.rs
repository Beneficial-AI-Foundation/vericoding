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

method Main() -> (result: bool)
{
    let arr1 = vec![0, 42, 0, 42];
    let res1 = acheck(arr1, 2);
    
    let arr2: Vec<int> = vec![];
    let res2 = acheck(arr2, 2);
    
    let arr3 = vec![0, 4, 2, 0];
    let res3 = acheck(arr3, 2);
    
    // Return one of the results (or combine them as needed)
    res1 && res2 && res3
}

}