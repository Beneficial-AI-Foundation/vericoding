pub fn DifferenceMinMax(a: &[i32]) -> (diff: i32)
    requires(a.len() > 0)
    ensures(|diff: i32| diff == (Max(a@) - Min(a@)))
{
}

pub spec fn Min(a: Seq<i32>) -> (m: i32)
    requires(a.len() > 0)
{
    if a.len() == 1 { a[0] }
    else {
        let minPrefix = Min(a.subrange(0, a.len() as int - 1));
        if a[a.len() - 1] <= minPrefix { a[a.len() - 1] } else { minPrefix }
    }
}

pub spec fn Max(a: Seq<i32>) -> (m: i32)
    requires(a.len() > 0)
{
    if a.len() == 1 { a[0] }
    else {
        let maxPrefix = Max(a.subrange(0, a.len() as int - 1));
        if a[a.len() - 1] >= maxPrefix { a[a.len() - 1] } else { maxPrefix }
    }
}