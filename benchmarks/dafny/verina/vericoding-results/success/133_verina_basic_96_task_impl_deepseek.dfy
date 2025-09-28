// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function abs(x: int): int {
  if x < 0 then -x else x
}

// </vc-helpers>

// <vc-spec>
method SwapSimultaneous(x: int, y: int) returns (result: (int, int))
    ensures
        result.0 == y &&
        result.1 == x &&
        (x != y ==> result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
{
  if x == y {
    result := (x, y);
  } else {
    result := (y, x);
  }
}
// </vc-code>
