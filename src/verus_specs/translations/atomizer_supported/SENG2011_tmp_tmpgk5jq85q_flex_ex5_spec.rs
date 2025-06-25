pub fn firste(a: &[char]) -> (c: i32)
    requires(
        true
    )
    ensures(|c: i32|
        -1 <= c && c < a.len() as i32 &&
        (0 <= c && c < a.len() as i32 ==> a[c as usize] == 'e' && forall|x: usize| 0 <= x && x < c as usize ==> a[x] != 'e') &&
        (c == -1 ==> forall|x: usize| 0 <= x && x < a.len() ==> a[x] != 'e')
    )
{
}

pub fn main()
{
}