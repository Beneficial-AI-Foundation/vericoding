use vstd::prelude::*;

verus! {

pub fn gaussian(size: int, q: &[f64], q_hat: &[f64]) -> &[f64]
    requires(
        q_hat.len() == size,
        q.len() == size,
        size > 0,
        arraySquaredSum(q_hat@) <= 1.0,
    )
{
}

pub closed spec fn arraySquaredSum(a: Seq<f64>) -> f64
    recommends(a.len() > 0)
{
    if a.len() == 1 {
        a[0] * a[0]
    } else {
        (a[0] * a[0]) + arraySquaredSum(a.subrange(1, a.len() as int))
    }
}

}