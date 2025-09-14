

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (min: int)
    ensures min <= a && min <= b && min <= c
    ensures (min == a) || (min == b) || (min == c)
// </vc-spec>
// <vc-code>
{
  var m := if a <= b && a <= c then a else if b <= a && b <= c then b else c;
  return m;
}
// </vc-code>

