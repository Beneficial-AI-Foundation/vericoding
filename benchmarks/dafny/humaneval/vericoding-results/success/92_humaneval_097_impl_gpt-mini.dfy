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
/* helper modified by LLM (iteration 3): prove UnitDigit in 0..9 */
lemma UnitDigitRange(n: int)
  ensures 0 <= UnitDigit(n) && UnitDigit(n) <= 9
{
  var m := if n >= 0 then n else -n;
  var u := m % 10;
  assert 0 <= u;
  assert u < 10;
  assert UnitDigit(n) == u;
}

/* helper modified by LLM (iteration 3): show product of unit digits in 0..81 */
lemma ProductOfUnitDigitsRange(a: int, b: int)
  ensures 0 <= ProductOfUnitDigits(a,b) && ProductOfUnitDigits(a,b) <= 81
{
  UnitDigitRange(a);
  UnitDigitRange(b);
  var ua := UnitDigit(a);
  var ub := UnitDigit(b);
  assert 0 <= ua && ua <= 9;
  assert 0 <= ub && ub <= 9;
  var p := ua * ub;
  assert 0 <= p && p <= 81;
  assert ProductOfUnitDigits(a,b) == p;
}

// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == ProductOfUnitDigits(a, b)
    ensures ValidResult(result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute product of unit digits and discharge range */
  result := ProductOfUnitDigits(a, b);
  ProductOfUnitDigitsRange(a, b);
  assert 0 <= result && result <= 81;
}

// </vc-code>
