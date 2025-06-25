pub fn count_arrays(arrays: Seq<&[i32]>) -> (count: i32)
    requires()
    ensures(count >= 0)
    ensures(count == arrays.len())
{
}