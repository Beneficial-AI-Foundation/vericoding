// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function sumTo(a: array<int>, n: int): int
  reads a
  requires 0 <= n <= a.Length
  decreases n
{
  if n == 0 then 0
  else sumTo(a, n - 1) + a[n - 1]
}

// </vc-helpers>

// <vc-spec>
method CumSum(a: array<int>) returns (result: array<int>)
    requires a.Length > 0
    ensures 
        result.Length == a.Length &&
        result[0] == a[0] &&
        forall i :: 1 <= i < a.Length ==> result[i] == result[i - 1] + a[i]
// </vc-spec>
// <vc-code>
{
    result := new int[a.Length];
    if a.Length > 0 {
        result[0] := a[0];
        var i := 1;
        while i < a.Length
            invariant 1 <= i <= a.Length
            invariant result[0] == a[0]
            invariant forall j :: 0 < j < i ==> result[j] == result[j - 1] + a[j]
        {
            result[i] := result[i - 1] + a[i];
            i := i + 1;
        }
    }
}
// </vc-code>
