predicate ValidInput(N: int, S: string)
{
    1 <= N <= 100 && |S| == N && forall i :: 0 <= i < |S| ==> 'a' <= S[i] <= 'z'
}

predicate IsConcatenationOfTwoCopies(S: string)
{
    |S| % 2 == 0 && forall i :: 0 <= i < |S|/2 ==> S[i] == S[|S|/2 + i]
}

// <vc-helpers>

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
    return;
  }
  if forall i :: 0 <= i < N/2 ==> S[i] == S[N/2 + i] {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

