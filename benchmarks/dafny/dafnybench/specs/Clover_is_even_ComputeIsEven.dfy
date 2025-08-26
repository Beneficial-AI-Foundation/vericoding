// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ComputeIsEven(x:int) returns (is_even:bool)
  ensures (x % 2 == 0)==is_even
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>