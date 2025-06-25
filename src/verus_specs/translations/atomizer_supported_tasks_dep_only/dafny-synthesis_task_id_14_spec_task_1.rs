pub fn triangular_prism_volume(base: int, height: int, length: int) -> (volume: int)
    requires(base > 0)
    requires(height > 0)
    requires(length > 0)
    ensures(|volume: int| volume == (base * height * length) / 2)
{
}