pub fn cubes(a: &mut [i32])
    ensures(forall|i: usize| 0 <= i < a.len() ==> a[i] == (i as i32) * (i as i32) * (i as i32))
{
}