

// <vc-helpers>
lemma AvgLemma(a: int, b: int)
  ensures (a + b) % 2 == 0 ==> (a + b) / 2 == (a + b) / 2
  ensures (a + b) % 2 != 0 ==> (a + b) / 2 == (a + b - 1) / 2
{
}
// </vc-helpers>

// <vc-spec>
method ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
// </vc-spec>
// <vc-code>
{
  avg := (a + b) / 2;
}
// </vc-code>

