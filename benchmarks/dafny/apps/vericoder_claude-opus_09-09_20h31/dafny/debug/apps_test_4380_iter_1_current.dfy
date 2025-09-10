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
lemma ProductOddIffAllOdd(x: int, y: int, z: int)
  ensures IsOdd(x * y * z) <==> (IsOdd(x) && IsOdd(y) && IsOdd(z))
{
  // A product is odd iff all factors are odd
}

lemma VerifyLogic(a: int, b: int)
  requires ValidInput(a, b)
  ensures ShouldAnswerYes(a, b) <==> ExistsOddProduct(a, b)
{
  if ShouldAnswerYes(a, b) {
    // a != 2 && b != 2, so both are in {1, 3}, hence both are odd
    assert a == 1 || a == 3;
    assert b == 1 || b == 3;
    assert IsOdd(a) && IsOdd(b);
    
    // Choose c = 1 (which is odd)
    var c := 1;
    assert 1 <= c <= 3;
    assert IsOdd(c);
    ProductOddIffAllOdd(a, b, c);
    assert IsOdd(a * b * c);
    assert ExistsOddProduct(a, b);
  } else {
    // Either a == 2 or b == 2, so at least one is even
    assert a == 2 || b == 2;
    
    // For any c in {1, 2, 3}, a * b * c will be even
    forall c | 1 <= c <= 3
      ensures !IsOdd(a * b * c)
    {
      if a == 2 || b == 2 {
        ProductOddIffAllOdd(a, b, c);
        assert !IsOdd(a) || !IsOdd(b);
        assert !IsOdd(a * b * c);
      }
    }
    assert !ExistsOddProduct(a, b);
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

