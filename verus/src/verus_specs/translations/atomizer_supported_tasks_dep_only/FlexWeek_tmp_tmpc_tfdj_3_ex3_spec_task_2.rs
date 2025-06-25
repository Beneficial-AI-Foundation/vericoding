// SPEC 
pub fn Max(a: &[nat]) -> m: int
    requires(true)
    ensures(a.len() > 0 ==> forall|k: int| 0 <= k < a.len() ==> m >= a[k as usize])
    ensures(a.len() == 0 ==> m == -1)
    ensures(a.len() > 0 ==> exists|i: int| 0 <= i < a.len() && m == a[i as usize])
{
}

// SPEC 
pub fn Checker()
    requires(true)
    ensures(true)
{
}