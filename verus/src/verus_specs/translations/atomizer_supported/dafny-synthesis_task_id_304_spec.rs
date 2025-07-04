pub fn element_at_index_after_rotation(l: Seq<int>, n: int, index: int) -> (element: int)
    requires 
        n >= 0,
        0 <= index < l.len(),
    ensures |element: int|
        element == l[(index - n + l.len()) % l.len()],
{
}