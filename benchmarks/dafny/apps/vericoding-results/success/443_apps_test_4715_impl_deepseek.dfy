predicate ValidInput(a: int, b: int, c: int)
{
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

function CountDistinctColors(a: int, b: int, c: int): int
{
    if a == b && b == c then 1
    else if a == b || b == c || a == c then 2
    else 3
}

predicate AllSame(a: int, b: int, c: int)
{
    a == b && b == c
}

predicate ExactlyTwoSame(a: int, b: int, c: int)
{
    (a == b && b != c) || (b == c && a != b) || (a == c && a != b)
}

predicate AllDifferent(a: int, b: int, c: int)
{
    a != b && b != c && a != c
}

// <vc-helpers>
lemma CountDistinctColorsProperties(a: int, b: int, c: int)
    requires ValidInput(a, b, c)
    ensures CountDistinctColors(a, b, c) == 1 <==> AllSame(a, b, c)
    ensures CountDistinctColors(a, b, c) == 2 <==> ExactlyTwoSame(a, b, c)
    ensures CountDistinctColors(a, b, c) == 3 <==> AllDifferent(a, b, c)
{
}

lemma ExactlyTwoSameImpliesNotAllSame(a: int, b: int, c: int)
    requires ExactlyTwoSame(a, b, c)
    ensures !AllSame(a, b, c)
{
}

lemma AllDifferentImpliesNotExactlyTwoSame(a: int, b: int, c: int)
    requires AllDifferent(a, b, c)
    ensures !ExactlyTwoSame(a, b, c)
{
}

lemma ExactlyTwoSameImpliesNotAllDifferent(a: int, b: int, c: int)
    requires ExactlyTwoSame(a, b, c)
    ensures !AllDifferent(a, b, c)
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures 1 <= result <= 3
    ensures result == CountDistinctColors(a, b, c)
    ensures result == 1 <==> AllSame(a, b, c)
    ensures result == 2 <==> ExactlyTwoSame(a, b, c)
    ensures result == 3 <==> AllDifferent(a, b, c)
// </vc-spec>
// <vc-code>
{
  CountDistinctColorsProperties(a, b, c);
  
  if a == b && b == c {
    result := 1;
  } else if a == b || b == c || a == c {
    result := 2;
  } else {
    result := 3;
  }
  
  // Verification helpers
  if (result == 1) {
    assert AllSame(a, b, c);
  } else if (result == 2) {
    assert ExactlyTwoSame(a, b, c);
    ExactlyTwoSameImpliesNotAllSame(a, b, c);
    ExactlyTwoSameImpliesNotAllDifferent(a, b, c);
  } else {
    assert AllDifferent(a, b, c);
    AllDifferentImpliesNotExactlyTwoSame(a, b, c);
  }
}
// </vc-code>

