predicate ValidInput(a: int, b: int)
{
    1 <= a <= 3 && 1 <= b <= 3
}

predicate IsOdd(n: int)
{
    n % 2 == 1
}

predicate ExistsOddProduct(a: int, b: int)
  requires ValidInput(a, b)
{
    exists c :: 1 <= c <= 3 && IsOdd(a * b * c)
}

function ShouldAnswerYes(a: int, b: int): bool
  requires ValidInput(a, b)
{
    a != 2 && b != 2
}

// <vc-helpers>
lemma OddProductExists(a: int, b: int)
  requires ValidInput(a, b)
  requires a != 2 && b != 2
  ensures ExistsOddProduct(a, b)
{
  if IsOdd(a * b) {
    assert IsOdd(a * b * 1);
    assert ExistsOddProduct(a, b);
  } else {
    assert IsOdd(a * b * 3);
    assert ExistsOddProduct(a, b);
  }
}

lemma NoOddProductWhenEven(a: int, b: int)
  requires ValidInput(a, b)
  requires a == 2 || b == 2
  ensures !ExistsOddProduct(a, b)
{
  forall c | 1 <= c <= 3 
    ensures !IsOdd(a * b * c)
  {
    assert (a * b * c) % 2 == 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
  requires ValidInput(a, b)
  ensures result == (if ShouldAnswerYes(a, b) then "Yes" else "No")
// </vc-spec>
// <vc-code>
{
  if a != 2 && b != 2 {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

