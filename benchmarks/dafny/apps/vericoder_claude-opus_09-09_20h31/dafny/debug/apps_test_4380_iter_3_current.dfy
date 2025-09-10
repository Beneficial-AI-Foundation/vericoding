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
  // This is because even * anything = even
  
  if IsOdd(x) && IsOdd(y) && IsOdd(z) {
    // All odd implies product is odd
    // x = 2k1 + 1, y = 2k2 + 1, z = 2k3 + 1
    var k1 := (x - 1) / 2;
    var k2 := (y - 1) / 2;
    var k3 := (z - 1) / 2;
    assert x == 2 * k1 + 1;
    assert y == 2 * k2 + 1;
    assert z == 2 * k3 + 1;
    
    // x * y = (2k1 + 1)(2k2 + 1) = 4k1k2 + 2k1 + 2k2 + 1 = 2(2k1k2 + k1 + k2) + 1
    assert x * y == 4 * k1 * k2 + 2 * k1 + 2 * k2 + 1;
    assert x * y == 2 * (2 * k1 * k2 + k1 + k2) + 1;
    assert (x * y) % 2 == 1;
    
    // (x * y) * z is odd * odd = odd
    var m := (x * y - 1) / 2;
    assert x * y == 2 * m + 1;
    assert x * y * z == (2 * m + 1) * (2 * k3 + 1);
    assert x * y * z == 4 * m * k3 + 2 * m + 2 * k3 + 1;
    assert x * y * z == 2 * (2 * m * k3 + m + k3) + 1;
    assert (x * y * z) % 2 == 1;
  }
  
  if !IsOdd(x) || !IsOdd(y) || !IsOdd(z) {
    // At least one even implies product is even
    if !IsOdd(x) {
      assert x % 2 == 0;
      var k := x / 2;
      assert x == 2 * k;
      assert x * y * z == 2 * k * y * z;
      assert (x * y * z) % 2 == 0;
    } else if !IsOdd(y) {
      assert y % 2 == 0;
      var k := y / 2;
      assert y == 2 * k;
      assert x * y * z == x * 2 * k * z;
      assert x * y * z == 2 * (x * k * z);
      assert (x * y * z) % 2 == 0;
    } else {
      assert !IsOdd(z);
      assert z % 2 == 0;
      var k := z / 2;
      assert z == 2 * k;
      assert x * y * z == x * y * 2 * k;
      assert x * y * z == 2 * (x * y * k);
      assert (x * y * z) % 2 == 0;
    }
    assert !IsOdd(x * y * z);
  }
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

