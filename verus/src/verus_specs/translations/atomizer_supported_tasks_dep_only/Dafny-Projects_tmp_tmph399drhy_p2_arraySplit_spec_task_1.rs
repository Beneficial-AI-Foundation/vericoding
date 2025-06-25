pub fn array_split(a: &[i32]) -> (Vec<i32>, Vec<i32>)
    ensures(|result: (Vec<i32>, Vec<i32>)| {
        let (b, c) = result;
        &&& a@ == b@ + c@
        &&& a.len() == b.len() + c.len()
        &&& a.len() > 1 ==> a.len() > b.len()
        &&& a.len() > 1 ==> a.len() > c.len()
    })
{
}