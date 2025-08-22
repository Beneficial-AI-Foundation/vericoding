//IMPL MinUnderSpec
method MinUnderSpec (x: int, y: int) returns (r: int)
    /* code modified by LLM (iteration 1): moved ensures clause to correct position before method body */
    ensures r <= x && r <= y
{
    /* code modified by LLM (iteration 1): implementation to satisfy the ensures clause */
    if x <= y {
        r := x;
    } else {
        r := y;
    }
}