pub fn symmetric(a: &[i32]) -> (flag: bool)
    ensures(
        flag == true ==> forall|x: usize| 0 <= x < a.len() ==> a[x] == a[a.len() - x - 1]
    )
    ensures(
        flag == false ==> exists|x: usize| 0 <= x < a.len() && a[x] != a[a.len() - x - 1]
    )
{
}

pub fn main()
{
}