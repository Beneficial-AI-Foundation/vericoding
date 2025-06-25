pub fn find(a: &[i32], key: i32) -> i32
    requires(true)
    ensures(|i: i32| 0 <= i ==> (i < a.len() && 
                                 a[i as usize] == key && 
                                 forall|k: usize| 0 <= k < i ==> a[k] != key))
    ensures(|i: i32| i < 0 ==> 
            forall|k: usize| 0 <= k < a.len() ==> a[k] != key)
{
}