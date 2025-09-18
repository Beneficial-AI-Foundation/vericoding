// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Mod2(x: int): int { x % 2 }
// </vc-helpers>

// <vc-spec>
method ComputeIsEven(x: int) returns (result: bool)
    ensures result == true <==> x % 2 == 0
// </vc-spec>
// <vc-code>
{
  var mod := Mod2(x);
  if mod == 0 {
    result := true;
  } else {
    result := false;
  }
}
// </vc-code>
