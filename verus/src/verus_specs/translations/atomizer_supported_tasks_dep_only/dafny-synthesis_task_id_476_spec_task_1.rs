pub fn SumMinMax(a: &[i32]) -> i32
    requires
        a.len() > 0,
    ensures |sum: i32|
        sum == Max(a) + Min(a),
{
}

pub fn Min(a: &[i32]) -> i32
    requires
        a.len() > 0,
{
    if a.len() == 1 {
        a[0]
    } else {
        let minPrefix = Min(&a[..a.len()-1]);
        if a[a.len()-1] <= minPrefix { a[a.len()-1] } else { Min(&a[..a.len()-1]) }
    }
}

pub fn Max(a: &[i32]) -> i32
    requires
        a.len() > 0,
{
    if a.len() == 1 {
        a[0]
    } else {
        let maxPrefix = Max(&a[..a.len()-1]);
        if a[a.len()-1] >= maxPrefix { a[a.len()-1] } else { Max(&a[..a.len()-1]) }
    }
}