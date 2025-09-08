Given a positive integer N and a string S of length N consisting of lowercase English letters,
determine whether S can be expressed as the concatenation of two identical strings (S = T + T for some string T).
Return "Yes" if S is a concatenation of two copies of some string; otherwise, return "No".

predicate ValidInput(N: int, S: string)
{
    1 <= N <= 100 && |S| == N && forall i :: 0 <= i < |S| ==> 'a' <= S[i] <= 'z'
}

predicate IsConcatenationOfTwoCopies(S: string)
{
    |S| % 2 == 0 && forall i :: 0 <= i < |S|/2 ==> S[i] == S[|S|/2 + i]
}

method solve(N: int, S: string) returns (result: string)
    requires ValidInput(N, S)
    ensures result == "Yes" || result == "No"
    ensures N % 2 != 0 ==> result == "No"
    ensures N % 2 == 0 ==> (result == "Yes" <==> IsConcatenationOfTwoCopies(S))
{
    if N % 2 != 0 {
        result := "No";
    } else {
        var m := N / 2;
        var i := 0;
        result := "Yes";
        while i < m
            invariant 0 <= i <= m
            invariant result == "Yes" || result == "No"
            invariant result == "Yes" ==> forall j :: 0 <= j < i ==> S[j] == S[m + j]
            invariant result == "No" ==> exists j :: 0 <= j < i && S[j] != S[m + j]
        {
            if S[i] != S[m + i] {
                result := "No";
                break;
            }
            i := i + 1;
        }
    }
}
