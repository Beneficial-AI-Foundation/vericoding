// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): ValidIndex predicate */
predicate ValidIndex(a: array<int>, i: int) reads a { 0 <= i < a.Length }

// </vc-helpers>

// <vc-spec>
method Argsort(a: array<int>) returns (result: array<int>)
    ensures result.Length == a.Length
    ensures forall i, j :: 0 <= i < j < result.Length && 0 <= result[i] < a.Length && 0 <= result[j] < a.Length ==> a[result[i]] <= a[result[j]]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): selection sort with explicit invariants proving initialization */
  var n := a.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall p :: 0 <= p < i ==> 0 <= result[p] < n
  {
    result[i] := i;
    i := i + 1;
  }
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall p :: 0 <= p < k ==> 0 <= result[p] < n
    invariant forall p :: k <= p < n ==> 0 <= result[p] < n
    invariant forall p,q :: 0 <= p < q < k ==> a[result[p]] <= a[result[q]]
    invariant forall p :: 0 <= p < k ==> forall q :: k <= q < n ==> a[result[p]] <= a[result[q]]
  {
    var m := k;
    var j := k + 1;
    while j < n
      invariant k <= m < n
      invariant k <= j <= n
      invariant forall t :: k <= t < j ==> a[result[m]] <= a[result[t]]
    {
      if a[result[j]] < a[result[m]] {
        m := j;
      }
      j := j + 1;
    }
    var tmp := result[k];
    result[k] := result[m];
    result[m] := tmp;
    k := k + 1;
  }
}

// </vc-code>
