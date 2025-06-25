pub fn CircleCircumference(radius: f64) -> (circumference: f64)
    requires(radius > 0.0)
    ensures(circumference == 2.0 * 3.14159265358979323846 * radius)
{
}