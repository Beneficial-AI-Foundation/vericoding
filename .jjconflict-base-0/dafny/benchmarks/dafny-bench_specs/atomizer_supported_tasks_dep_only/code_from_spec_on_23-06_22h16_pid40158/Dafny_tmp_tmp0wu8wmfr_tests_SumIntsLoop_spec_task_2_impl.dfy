/* code modified by LLM (iteration 1): Added decreases clause and proper handling of negative inputs to ensure termination and correct behavior */
function sumInts( n: int ): int
  decreases if n <= 0 then 0 else n
{
    if n <= 0 then
        0
    else
        sumInts(n-1)+n
}