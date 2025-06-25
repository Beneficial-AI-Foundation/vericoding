pub fn single(x: &[i32], y: &[i32]) -> Vec<i32>
    requires(
        x.len() > 0,
        y.len() > 0,
    )
    ensures(|result: Vec<i32>| 
        result@ == x@ + y@
    )
{
    todo!()
}