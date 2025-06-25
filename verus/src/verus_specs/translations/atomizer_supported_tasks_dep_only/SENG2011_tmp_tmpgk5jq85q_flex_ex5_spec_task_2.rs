pub fn firste(a: &[char]) -> (c: i32)
    requires(
        true
    )
    ensures(|c: i32|
        -1 <= c && c < a.len() as i32 &&
        (0 <= c && c < a.len() as i32 ==> a[c as usize] == 'e' && forall|x: i32| 0 <= x && x < c ==> a[x as usize] != 'e') &&
        (c == -1 ==> forall|x: i32| 0 <= x && x < a.len() as i32 ==> a[x as usize] != 'e')
    )
{
}

pub fn main()
{
}