pub fn gaussian(size: int, q: &[real], q_hat: &[real]) -> Vec<real>
    requires
        q_hat.len() == size,
        q.len() == size,
        size > 0,
        arraySquaredSum(q_hat) <= 1.0,
    ensures
{
}

pub fn arraySquaredSum(a: &[real]) -> real
    requires
        a.len() > 0,
{
    if a.len() == 1 {
        a[0] * a[0]
    } else {
        (a[0] * a[0]) + arraySquaredSum(&a[1..])
    }
}