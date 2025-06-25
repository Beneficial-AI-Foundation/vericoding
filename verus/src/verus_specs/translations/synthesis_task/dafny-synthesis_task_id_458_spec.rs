pub fn RectangleArea(length: int, width: int) -> (area: int)
    requires(length > 0)
    requires(width > 0)
    ensures(|area: int| area == length * width)
{
}