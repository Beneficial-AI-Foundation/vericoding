function ProductOfDigits(x: int): int
  requires x >= 0
{
  if x == 0 then 1
  else if x < 10 then x
  else (x % 10) * ProductOfDigits(x / 10)
}

function MaxProductOfDigitsInRange(n: int): int
  requires n >= 1
{
  if n == 1 then 1
  else
    var current := ProductOfDigits(n);
    var rest := MaxProductOfDigitsInRange(n - 1);
    if current > rest then current else rest
}

// <vc-helpers>
// Léxico y propiedades para verificar ProductOfDigits
lemma DigitProductNonNegative(x: int)
  requires x >= 0
  ensures ProductOfDigits(x) >= 0
{
  if x < 10 {
    if x == 0 {
    } else {
    }
  } else {
    var q := x / 10;
    DigitProductNonNegative(q);
  }
}

lemma DigitProductForSingleDigit(x: int)
  requires 0 <= x < 10
  ensures ProductOfDigits(x) == if x == 0 then 1 else x
{
  if x == 0 {
  } else {
  }
}

lemma DigitProductRecursiveProperty(n: int)
  requires n >= 10
  ensures ProductOfDigits(n) == (n % 10) * ProductOfDigits(n / 10)
{
}

// Définition alternativa pour verifier la boucle
function MaxProductUpTo(k: int, upper: int): int
  requires 1 <= k <= upper + 1
  decreases upper - k + 1
{
  if k == upper + 1 then 0
  else {
    var prod := ProductOfDigits(k);
    var rest := MaxProductUpTo(k + 1, upper);
    if prod > rest then prod else rest
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 1
  ensures result == MaxProductOfDigitsInRange(n)
  ensures result >= 1
  ensures forall k :: 1 <= k <= n ==> ProductOfDigits(k) <= result
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == result
// </vc-spec>
// <vc-code>
{
  var result := 0;
  for k := 1 to n
    invariant 1 <= k <= n + 1
    invariant result == MaxProductUpTo(1, k - 1)
  {
    var p := ProductOfDigits(k);
    if p > result {
      result := p;
    }
  }
}
// </vc-code>

