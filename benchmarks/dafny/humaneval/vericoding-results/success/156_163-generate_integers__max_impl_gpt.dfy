// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function maxVal(a: int, b: int): int { if a >= b then a else b }

lemma MaxValIsMember(a: int, b: int)
  ensures maxVal(a, b) == a || maxVal(a, b) == b
{ }

lemma MaxValGe(a: int, b: int)
  ensures maxVal(a, b) >= a && maxVal(a, b) >= b
{ }
// </vc-helpers>

// <vc-spec>
method max(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m >= a && m >= b
// </vc-spec>
// <vc-code>
{
  if a >= b {
    m := a;
  } else {
    m := b;
  }
}
// </vc-code>
