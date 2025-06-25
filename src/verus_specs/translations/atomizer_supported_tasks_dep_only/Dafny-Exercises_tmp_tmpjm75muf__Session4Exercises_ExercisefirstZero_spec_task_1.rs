pub fn mfirstCero(v: &[i32]) -> (i: i32)
    ensures(0 <= i <= v.len())
    ensures(forall|j: i32| 0 <= j < i ==> v[j as usize] != 0)
    ensures(i != v.len() ==> v[i as usize] == 0)
{
}