

// <vc-helpers>
lemma DivModLemma(a: int, b: int)
  requires b != 0
  ensures a == (a / b) * b + (a % b)
  ensures 0 <= a % b < (if b < 0 then -b else b)
{
}

lemma DivModLemmaFor191()
  ensures 191 == 27 * 7 + 2
  ensures 0 <= 2 < 7
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method CalDiv() returns (x:int, y:int)
  ensures x==191/7
  ensures y==191%7
// </vc-spec>
// <vc-code>
{
  DivModLemma(191, 7);
  DivModLemmaFor191();
  x := 27;
  y := 2;
}
// </vc-code>

