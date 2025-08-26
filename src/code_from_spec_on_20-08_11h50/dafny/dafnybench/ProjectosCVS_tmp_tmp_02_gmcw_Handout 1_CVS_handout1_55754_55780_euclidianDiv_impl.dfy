lemma peasantMultLemma(a:int, b:int)
    requires b >= 0
    ensures b % 2 == 0 ==> (a * b == 2 * a * b / 2)
    ensures b % 2 == 1 ==> (a * b == a + 2 * a * (b - 1) / 2)
    {
        if (b % 2 == 0 && b > 0) { 
            peasantMultLemma(a, b - 2);
        }

        if (b % 2 == 1 && b > 1) {
            peasantMultLemma(a, b - 2);
        }

    }



//Second Exercise

// <vc-helpers>
// </vc-helpers>

method euclidianDiv(a: int,b : int) returns (q: int,r: int)
    requires a >= 0
    requires b > 0
    ensures a == b * q + r
// </vc-spec>
// <vc-code>
{
  q := 0;
  r := a;
  while r >= b
    invariant a == b * q + r
    invariant r >= 0
    decreases r
  {
    r := r - b;
    q := q + 1;
  }
}
// </vc-code>