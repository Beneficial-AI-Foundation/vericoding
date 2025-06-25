pub fn triangular_prism_volume(base: int, height: int, length: int) -> (volume: int)
    requires
        base > 0,
        height > 0,
        length > 0,
    ensures
        volume == (base * height * length) / 2,
{
}