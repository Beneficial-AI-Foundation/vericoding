// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define intersection set of arrays */
function IntersectionSet(a: array<real>, b: array<real>): set<real> reads a, b {
  { x | x in a[..] && x in b[..] }
}

/* helper modified by LLM (iteration 5): cardinality of distinct prefix equals prefix length */
lemma DistinctArrayCardinality(arr: array<real>, k: int)
  requires 0 <= k <= arr.Length
  requires forall p, q :: 0 <= p < q < k ==> arr[p] != arr[q]
  ensures |{ x | exists t :: 0 <= t < k && arr[t] == x }| == k
{
  if k == 0 {
    // empty prefix: set is empty
  } else {
    DistinctArrayCardinality(arr, k-1);
    assert !(exists t :: 0 <= t < k-1 && arr[t] == arr[k-1]);
    var prev := { x | exists t :: 0 <= t < k-1 && arr[t] == x };
    assert arr[k-1] !in prev;
    assert { x | exists t :: 0 <= t < k && arr[t] == x } == prev + { arr[k-1] };
    assert |prev + { arr[k-1] }| == |prev| + 1;
    assert |{ x | exists t :: 0 <= t < k && arr[t] == x }| == (k-1) + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method Intersect(a: array<real>, b: array<real>) returns (result: array<real>)
    ensures
        result.Length < a.Length && result.Length < b.Length &&
        forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> (
            (a[i] == b[j] ==> exists k :: 0 <= k < result.Length && result[k] == a[i]) &&
            (a[i] != b[j] ==> !exists k :: 0 <= k < result.Length && result[k] == a[i])
        )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build array of unique intersection elements with strong invariants to prove completeness */
  var s := IntersectionSet(a, b);
  var n := |s|;
  result := new real[n];
  var k := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= k <= n
    invariant forall idx :: 0 <= idx < k ==> result[idx] in s
    invariant forall p, q :: 0 <= p < q < k ==> result[p] != result[q]
    invariant forall x :: x in s && (exists t :: 0 <= t < i && a[t] == x) ==> (exists t :: 0 <= t < k && result[t] == x)
    decreases a.Length - i
  {
    if a[i] in s {
      var j := 0;
      var found := false;
      while j < k
        invariant 0 <= j <= k
        invariant found <==> (exists t :: 0 <= t < j && result[t] == a[i])
      {
        if result[j] == a[i] { found := true; }
        j := j + 1;
      }
      if !found {
        if k < n {
          result[k] := a[i];
          k := k + 1;
        }
      }
    }
    i := i + 1;
  }
  // establish that result contains exactly the intersection set
  assert forall x :: x in s ==> (exists t :: 0 <= t < k && result[t] == x);
  assert forall idx :: 0 <= idx < k ==> result[idx] in s;
  // distinctness gives cardinality equality for the prefix
  DistinctArrayCardinality(result, k);
  assert |{ x | exists t :: 0 <= t < k && result[t] == x }| == k;
  // since every result element is in s, k <= n
  assert k <= n;
  // since every element of s appears in result, n <= k
  assert n <= k;
  assert k == n;
}
// </vc-code>
