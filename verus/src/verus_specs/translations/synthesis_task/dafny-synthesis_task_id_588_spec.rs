pub fn DifferenceMinMax(a: &[i32]) -> (diff: i32)
    requires
        a.len() > 0,
    ensures |diff: i32|
        diff == Max(a@) - Min(a@),
{
}

pub open spec fn Min(a: Seq<i32>) -> i32
    recommends
        a.len() > 0,
{
    if a.len() == 1 {
        a[0]
    } else {
        let minPrefix = Min(a.subrange(0, a.len() - 1));
        if a[a.len() - 1] <= minPrefix {
            a[a.len() - 1]
        } else {
            Min(a.subrange(0, a.len() - 1))
        }
    }
}

pub open spec fn Max(a: Seq<i32>) -> i32
    recommends
        a.len() > 0,
{
    if a.len() == 1 {
        a[0]
    } else {
        let maxPrefix = Max(a.subrange(0, a.len() - 1));
        if a[a.len() - 1] >= maxPrefix {
            a[a.len() - 1]
        } else {
            Max(a.subrange(0, a.len() - 1))
        }
    }
}