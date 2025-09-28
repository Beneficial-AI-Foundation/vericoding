// <vc-preamble>
predicate ValidInput(N: int, S: string)
{
    1 <= N <= 100 && |S| == N && forall i :: 0 <= i < |S| ==> 'a' <= S[i] <= 'z'
}

predicate IsConcatenationOfTwoCopies(S: string)
{
    |S| % 2 == 0 && forall i :: 0 <= i < |S|/2 ==> S[i] == S[|S|/2 + i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed incorrect syntax around 'takes' for string slicing, which is not a Dafny feature. Replaced with correct Dafny string slicing for functions. */
function GetFirstHalf(S: string): string {
    S[0 .. |S|/2]
}

function GetSecondHalf(S: string): string {
    S[|S|/2 .. |S|]
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
/* code modified by LLM (iteration 2): Implemented the logic to check if a string is a concatenation of two copies by comparing its first and second halves. Handles odd length cases as specified. */
{
  if N % 2 != 0 {
    result := "No";
    return;
  }

  var firstHalf := S[0 .. N/2];
  var secondHalf := S[N/2 .. N];

  if firstHalf == secondHalf {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>
