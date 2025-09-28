// <vc-preamble>

function UnitDigit(n: int): int
{
    (if n >= 0 then n else -n) % 10
}

function ProductOfUnitDigits(a: int, b: int): int
{
    UnitDigit(a) * UnitDigit(b)
}

predicate ValidResult(result: int)
{
    result >= 0 && result <= 81
}
// </vc-preamble>

// <vc-helpers>
lemma UnitDigitRange(n: int)
  ensures 0 <= UnitDigit(n) <= 9
{
  assert 0 <= UnitDigit(n);
  assert UnitDigit(n) < 10;
}

lemma MultMonotoneLeft_Nat(x: int, y: int, z: nat)
  requires x <= y
  ensures x * z <= y * z
  decreases z
{
  if z > 0 {
    var k: nat := z - 1;
    MultMonotoneLeft_Nat(x, y, k);
    assert k + 1 == z;
    assert x * z == x * k + x;
    assert y * z == y * k + y;
    assert x * k + x <= y * k + y;
  }
}

lemma ProductOfUnitDigitsBound(a: int, b: int)
  ensures ValidResult(ProductOfUnitDigits(a, b))
{
  var da := UnitDigit(a);
  var db := UnitDigit(b);
  UnitDigitRange(a);
  UnitDigitRange(b);
  assert 0 <= db;
  var dbn: nat := db;
  // Lower bound
  MultMonotoneLeft_Nat(0, da, dbn);
  assert 0 * dbn == 0;
  assert 0 <= da * db;
  // Upper bound
  MultMonotoneLeft_Nat(da, 9, dbn);
  MultMonotoneLeft_Nat(db, 9, 9);
  assert 9 * 9 == 81;
  assert db * 9 <= 81;
  assert 9 * db == db * 9;
  calc {
    da * db;
    <= { }
    9 * db;
    == { }
    db * 9;
    <= { }
    81;
  }
  assert ProductOfUnitDigits(a, b) == da * db;
  assert ValidResult(ProductOfUnitDigits(a, b));
}
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == ProductOfUnitDigits(a, b)
    ensures ValidResult(result)
// </vc-spec>
// <vc-code>
{
  result := ProductOfUnitDigits(a, b);
  ProductOfUnitDigitsBound(a, b);
}
// </vc-code>
