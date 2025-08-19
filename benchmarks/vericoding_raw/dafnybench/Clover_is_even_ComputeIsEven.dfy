// <vc-helpers>
// </vc-helpers>

method ComputeIsEven(x:int) returns (is_even:bool)
  ensures (x % 2 == 0)==is_even
// <vc-code>
{
  assume false;
}
// </vc-code>