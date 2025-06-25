use vstd::prelude::*;

verus! {

//Given an array of natural numbers, it returns the maximum value. [5,1,3,6,12,3]->12

// SPEC 
//Given an array of natural numbers, it returns the maximum value. [5,1,3,6,12,3]->12

pub fn max(x: &[nat]) -> (y: nat)
    // for index loop problems
    requires(x.len() > 0)
    // ensuring that we maintain y as greater than the elements in the array 
    ensures(forall|j: int| 0 <= j < x.len() ==> y >= x[j as usize])
    // ensuring that the return value is in the array
    ensures(exists|i: int| 0 <= i < x.len() && y == x[i as usize])
{
}

// SPEC 

pub fn Main()
{
}

}