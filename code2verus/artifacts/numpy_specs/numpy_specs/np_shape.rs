use vstd::prelude::*;

verus! {

// SPEC
pub enum Arrays {
    ArrayOne { arr1: Vec<i32> },
    ArrayTwo { arr2: Vec<Vec<i32>> },
    ArrayThree { arr3: Vec<Vec<Vec<i32>>> },
}

// SPEC
pub fn shape_prime_prime(a: &Arrays) -> (ret: Vec<usize>)
    ensures
        match a {
            Arrays::ArrayOne { arr1 } => ret.len() == 1 && ret[0] == arr1.len(),
            Arrays::ArrayTwo { arr2 } => {
                ret.len() == 2 && 
                ret[0] == arr2.len() && 
                ret[1] == (if arr2.len() > 0 { arr2[0].len() } else { 0 })
            },
            Arrays::ArrayThree { arr3 } => {
                ret.len() == 3 && 
                ret[0] == arr3.len() && 
                ret[1] == (if arr3.len() > 0 { arr3[0].len() } else { 0 }) && 
                ret[2] == (if arr3.len() > 0 && arr3[0].len() > 0 { arr3[0][0].len() } else { 0 })
            },
        }
{
    match a {
        Arrays::ArrayOne { arr1 } => {
            vec![arr1.len()]
        },
        Arrays::ArrayTwo { arr2 } => {
            let dim1 = if arr2.len() > 0 { arr2[0].len() } else { 0 };
            vec![arr2.len(), dim1]
        },
        Arrays::ArrayThree { arr3 } => {
            let dim1 = if arr3.len() > 0 { arr3[0].len() } else { 0 };
            let dim2 = if arr3.len() > 0 && arr3[0].len() > 0 { arr3[0][0].len() } else { 0 };
            vec![arr3.len(), dim1, dim2]
        }
    }
}

// SPEC  
pub fn shape(a: &Vec<Vec<i32>>) -> (ret: Vec<usize>)
    ensures
        ret.len() == 2 &&
        ret[0] == a.len() &&
        ret[1] == (if a.len() > 0 { a[0].len() } else { 0 })
{
    let dim1 = if a.len() > 0 { a[0].len() } else { 0 };
    vec![a.len(), dim1]
}

}