pub fn gaussian(size: int, q: &[f64], q_hat: &[f64]) -> Vec<f64>
    requires
        q_hat.len() == size,
        q.len() == size,
        size > 0,
        arraySquaredSum(q_hat) <= 1.0,
{
    todo!()
}

pub fn arraySquaredSum(a: &[f64]) -> f64
    requires a.len() > 0
    decreases a.len()
{
    if a.len() == 1 {
        a[0] * a[0]
    } else {
        (a[0] * a[0]) + arraySquaredSum(&a[1..])
    }
}