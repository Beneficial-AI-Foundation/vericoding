//Algorithm 1: From left to right return the first
// SPEC 
//Algorithm 1: From left to right return the first
pub fn mmaximum1(v: &[i32]) -> i32
    requires(v.len() > 0)
    ensures(|i: i32| 0 <= i < v.len())
    ensures(|i: i32| forall|k: usize| 0 <= k < v.len() ==> v[i as usize] >= v[k])
{
}

//Algorithm 2: From right to left return the last
// SPEC 

//Algorithm 2: From right to left return the last
pub fn mmaximum2(v: &[i32]) -> i32
    requires(v.len() > 0)
    ensures(|i: i32| 0 <= i < v.len())
    ensures(|i: i32| forall|k: usize| 0 <= k < v.len() ==> v[i as usize] >= v[k])
{
}

// SPEC 

pub fn mfirstMaximum(v: &[i32]) -> i32
    requires(v.len() > 0)
    ensures(|i: i32| 0 <= i < v.len())
    ensures(|i: i32| forall|k: usize| 0 <= k < v.len() ==> v[i as usize] >= v[k])
    ensures(|i: i32| forall|l: usize| 0 <= l < i ==> v[i as usize] > v[l])
//Algorithm: from left to right
{
}

// SPEC 

pub fn mlastMaximum(v: &[i32]) -> i32
    requires(v.len() > 0)
    ensures(|i: i32| 0 <= i < v.len())
    ensures(|i: i32| forall|k: usize| 0 <= k < v.len() ==> v[i as usize] >= v[k])
    ensures(|i: i32| forall|l: usize| i < l < v.len() ==> v[i as usize] > v[l])
{
}

//Algorithm : from left to right
//Algorithm : from right to left

// SPEC 

//Algorithm : from left to right
//Algorithm : from right to left

pub fn mmaxvalue1(v: &[i32]) -> i32
    requires(v.len() > 0)
    ensures(|m: i32| exists|k: usize| 0 <= k < v.len() && m == v[k])
    ensures(|m: i32| forall|k: usize| 0 <= k < v.len() ==> m >= v[k])
{
}

// SPEC 

pub fn mmaxvalue2(v: &[i32]) -> i32
    requires(v.len() > 0)
    ensures(|m: i32| exists|k: usize| 0 <= k < v.len() && m == v[k])
    ensures(|m: i32| forall|k: usize| 0 <= k < v.len() ==> m >= v[k])
{
}