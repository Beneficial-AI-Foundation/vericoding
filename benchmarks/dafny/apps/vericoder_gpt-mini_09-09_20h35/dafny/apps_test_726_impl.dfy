predicate ValidInput(n: int, d: int, hotels: seq<int>)
{
    n > 0 && d > 0 && |hotels| == n &&
    (forall i :: 0 <= i < n - 1 ==> hotels[i] < hotels[i + 1])
}

function SumContributions(hotels: seq<int>, d: int, i: int): int
    requires 0 <= i <= |hotels| - 1
    requires d > 0
    requires forall j :: 0 <= j < |hotels| - 1 ==> hotels[j] < hotels[j + 1]
{
    if i == 0 then 0
    else
        var gap := hotels[i] - hotels[i-1];
        var contribution := if gap == 2*d then 1 else if gap > 2*d then 2 else 0;
        contribution + SumContributions(hotels, d, i-1)
}

predicate CorrectResult(n: int, d: int, hotels: seq<int>, result: int)
    requires ValidInput(n, d, hotels)
{
    result == 2 + SumContributions(hotels, d, n-1) && result >= 2
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, d: int, hotels: seq<int>) returns (result: int)
    requires ValidInput(n, d, hotels)
    ensures CorrectResult(n, d, hotels, result)
// </vc-spec>
// <vc-code>
{
  var acc := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant acc == SumContributions(hotels, d, i)
    decreases n - 1 - i
  {
    var gap := hotels[i+1] - hotels[i];
    var c := if gap == 2 * d then 1 else if gap > 2 * d then 2 else 0;
    acc := acc + c;
    i := i + 1;
  }
  result := 2 + acc;
  assert result >= 2;
  assert result == 2 + SumContributions(hotels, d, n - 1);
}
// </vc-code>

