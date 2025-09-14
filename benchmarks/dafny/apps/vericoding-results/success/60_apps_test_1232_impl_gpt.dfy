predicate ValidInput(n_A: int, n_B: int, k: int, m: int, A: seq<int>, B: seq<int>)
{
    n_A >= 1 && n_B >= 1 &&
    k >= 1 && k <= n_A &&
    m >= 1 && m <= n_B &&
    |A| == n_A &&
    |B| == n_B
}

predicate IsSorted(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

predicate ValidSelection(A: seq<int>, B: seq<int>, k: int, m: int)
    requires k >= 1 && k <= |A|
    requires m >= 1 && m <= |B|
{
    A[k - 1] < B[|B| - m]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n_A: int, n_B: int, k: int, m: int, A: seq<int>, B: seq<int>) returns (result: string)
    requires ValidInput(n_A, n_B, k, m, A, B)
    requires IsSorted(A)
    requires IsSorted(B)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> ValidSelection(A, B, k, m)
// </vc-spec>
// <vc-code>
{
  assert k >= 1;
  assert k <= |A|;
  assert m >= 1;
  assert m <= |B|;

  assert 0 <= k - 1;
  assert k - 1 <= |A| - 1;
  assert |A| - 1 < |A|;
  assert 0 <= |B| - m;
  assert |B| - m <= |B| - 1;
  assert |B| - 1 < |B|;

  var cond := A[k - 1] < B[|B| - m];
  if cond {
    result := "YES";
  } else {
    result := "NO";
  }

  assert ValidSelection(A, B, k, m) <==> (A[k - 1] < B[|B| - m]);
  assert (result == "YES") <==> cond;
  assert result == "YES" || result == "NO";
  assert (result == "YES") <==> ValidSelection(A, B, k, m);
}
// </vc-code>

