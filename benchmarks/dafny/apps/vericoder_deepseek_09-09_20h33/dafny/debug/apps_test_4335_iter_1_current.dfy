predicate ValidInput(N: int, S: string)
{
    1 <= N <= 100 && |S| == N && forall i :: 0 <= i < |S| ==> 'a' <= S[i] <= 'z'
}

predicate IsConcatenationOfTwoCopies(S: string)
{
    |S| % 2 == 0 && forall i :: 0 <= i < |S|/2 ==> S[i] == S[|S|/2 + i]
}

// <vc-helpers>
lemma LemmaSplitEqualHalves(S: string, n: int)
  requires |S| == 2 * n
  requires forall i :: 0 <= i < n ==> S[i] == S[n + i]
  ensures S[0..n] == S[n..2*n]
{
}

lemma LemmaUnequalIfDifferentChar(S: string, n: int, k: int)
  requires 0 <= k < n
  requires S[k] != S[n + k]
  ensures S[0..n] != S[n..2*n]
{
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, S: string) returns (result: string)
    requires ValidInput(N, S)
    ensures result == "Yes" || result == "No"
    ensures N % 2 != 0 ==> result == "No"
    ensures N % 2 == 0 ==> (result == "Yes" <==> IsConcatenationOfTwoCopies(S))
// </vc-spec>
// <vc-code>
{
  if N % 2 != 0 {
    result := "No";
  } else {
    var half := N / 2;
    var foundDiff := false;
    var i := 0;
    while i < half
      invariant 0 <= i <= half
      invariant !foundDiff ==> forall j :: 0 <= j < i ==> S[j] == S[half + j]
      invariant foundDiff ==> exists j :: 0 <= j < i && S[j] != S[half + j]
    {
      if S[i] != S[half + i] {
        foundDiff := true;
      }
      i := i + 1;
    }
    
    if foundDiff {
      result := "No";
    } else {
      result := "Yes";
    }
  }
}
// </vc-code>

