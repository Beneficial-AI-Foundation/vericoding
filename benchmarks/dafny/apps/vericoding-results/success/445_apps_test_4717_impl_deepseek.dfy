predicate ValidInput(x: int, a: int, b: int)
{
    1 <= x <= 1000 &&
    1 <= a <= 1000 &&
    1 <= b <= 1000 &&
    x != a && x != b && a != b &&
    Distance(x, a) != Distance(x, b)
}

function Distance(s: int, t: int): nat
{
    if s >= t then s - t else t - s
}

predicate CorrectResult(x: int, a: int, b: int, result: string)
{
    (result == "A" <==> Distance(x, a) < Distance(x, b)) &&
    (result == "B" <==> Distance(x, b) < Distance(x, a))
}

// <vc-helpers>
lemma DistanceNonNegative(s: int, t: int)
ensures Distance(s, t) >= 0
{
}

lemma DistanceProperties(s: int, t: int)
ensures Distance(s, t) == Distance(t, s)
ensures Distance(s, t) >= 0
{
}

lemma DistanceComparison(s: int, t: int, u: int)
requires s != t && s != u && t != u
requires Distance(s, t) != Distance(s, u)
ensures (Distance(s, t) < Distance(s, u)) || (Distance(s, u) < Distance(s, t))
{
}
// </vc-helpers>

// <vc-spec>
method solve(x: int, a: int, b: int) returns (result: string)
requires ValidInput(x, a, b)
ensures result == "A" || result == "B"
ensures CorrectResult(x, a, b, result)
// </vc-spec>
// <vc-code>
{
  var distA := Distance(x, a);
  var distB := Distance(x, b);
  if distA < distB {
    result := "A";
  } else {
    result := "B";
  }
}
// </vc-code>

