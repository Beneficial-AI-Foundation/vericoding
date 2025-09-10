predicate ValidInput(N: int, S: string)
{
    1 <= N <= 100 && |S| == N && forall i :: 0 <= i < |S| ==> 'a' <= S[i] <= 'z'
}

predicate IsConcatenationOfTwoCopies(S: string)
{
    |S| % 2 == 0 && forall i :: 0 <= i < |S|/2 ==> S[i] == S[|S|/2 + i]
}

// <vc-helpers>
lemma lemma_string_split(s: string)
  requires |s| % 2 == 0
  ensures |s|/2 + |s|/2 == |s|
{ }
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
    return "No";
  } else {
    lemma_string_split(S); 

    var isConcatenation := true;
    for i := 0 to N/2 - 1
      invariant 0 <= i <= N/2
      invariant isConcatenation == (forall j :: 0 <= j < i ==> S[j] == S[N/2 + j])
    {
      if S[i] != S[N/2 + i] {
        isConcatenation := false;
        break;
      }
    }

    if isConcatenation {
      return "Yes";
    } else {
      return "No";
    }
  }
}
// </vc-code>

