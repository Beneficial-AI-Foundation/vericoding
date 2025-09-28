// <vc-preamble>
function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: int) returns (count: int)
    requires a >= 0
    ensures count >= 0
    ensures count == CountOnesInOctal(a)
// </vc-spec>
// <vc-code>
{
  var temp_a := a;
  count := 0;
  while temp_a > 0
    invariant temp_a >= 0
    invariant count + CountOnesInOctal(temp_a) == CountOnesInOctal(a)
  {
    if temp_a % 8 == 1 {
      count := count + 1;
    }
    temp_a := temp_a / 8;
  }
}
// </vc-code>
