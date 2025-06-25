// Finds the maximum value in a non-empty array.
pub fn findMax(a: &[f64]) -> (max: f64)
    requires a.len() > 0
    ensures exists|k: usize| 0 <= k < a.len() && max == a[k]
    ensures forall|k: usize| 0 <= k < a.len() ==> max >= a[k]
{
}