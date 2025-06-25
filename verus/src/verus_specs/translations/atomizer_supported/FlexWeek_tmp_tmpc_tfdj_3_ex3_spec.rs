pub fn max(a: &[nat]) -> (m: i32)
    requires(true)
    ensures(|result: i32| a.len() > 0 ==> (forall|k: usize| 0 <= k < a.len() ==> result >= a[k]))
    ensures(|result: i32| a.len() == 0 ==> result == -1)
    ensures(|result: i32| a.len() > 0 ==> exists|k: usize| 0 <= k < a.len() && result == a[k])
{
}

pub fn checker()
    requires(true)
    ensures(true)
{
}