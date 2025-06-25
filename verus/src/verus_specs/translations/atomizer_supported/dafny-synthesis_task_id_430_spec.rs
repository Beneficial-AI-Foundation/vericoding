pub fn ParabolaDirectrix(a: f64, h: f64, k: f64) -> (directrix: f64)
    requires(a != 0.0)
    ensures(|directrix: f64| directrix == k - 1.0 / (4.0 * a))
{
}