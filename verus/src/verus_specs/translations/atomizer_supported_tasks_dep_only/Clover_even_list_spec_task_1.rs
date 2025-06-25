pub fn find_even_numbers(arr: &[i32]) -> Vec<i32>
    ensures(forall|x: i32| arr.contains(&x) && (x % 2 == 0) ==> result@.contains(&x))
    ensures(forall|x: i32| !arr.contains(&x) ==> !result@.contains(&x))
    ensures(forall|k: int| 0 <= k < result@.len() ==> result@[k] % 2 == 0)
    ensures(forall|k: int, l: int| 0 <= k < l < result@.len() ==>
        exists|n: int, m: int| 0 <= n < m < arr.len() && result@[k] == arr[n] && result@[l] == arr[m])
{
}