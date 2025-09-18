// <vc-preamble>
function abs(x: int): int
{
    if x >= 0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
lemma AbsSpec(x: int)
  ensures (x >= 0 ==> abs(x) == x) && (x < 0 ==> x + abs(x) == 0)
{
  if x >= 0 {
    assert abs(x) == x;
  } else {
    assert x + abs(x) == 0;
  }
}
// </vc-helpers>

// <vc-spec>
method abs_impl(x: int) returns (result: int)
    ensures (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0)
// </vc-spec>
// <vc-code>
{
  result := abs(x);
}
// </vc-code>
