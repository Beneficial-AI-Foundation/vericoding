predicate ValidInput(N: int, S: string)
{
    1 <= N <= 100 && |S| == N && forall i :: 0 <= i < |S| ==> 'a' <= S[i] <= 'z'
}

predicate IsConcatenationOfTwoCopies(S: string)
{
    |S| % 2 == 0 && forall i :: 0 <= i < |S|/2 ==> S[i] == S[|S|/2 + i]
}

// <vc-helpers>
lemma ConcatenationImpliesEqualHalves(S: string)
    requires |S| % 2 == 0
    requires IsConcatenationOfTwoCopies(S)
    ensures forall i :: 0 <= i < |S|/2 ==> S[i] == S[|S|/2 + i]
{
    // This follows directly from the definition of IsConcatenationOfTwoCopies
}

lemma EqualHalvesImpliesConcatenation(S: string)
    requires |S| % 2 == 0
    requires forall i :: 0 <= i < |S|/2 ==> S[i] == S[|S|/2 + i]
    ensures IsConcatenationOfTwoCopies(S)
{
    // This follows directly from the definition of IsConcatenationOfTwoCopies
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
        var isConcat := true;
        var i := 0;
        
        while i < N/2
            invariant 0 <= i <= N/2
            invariant isConcat <==> (forall j :: 0 <= j < i ==> S[j] == S[N/2 + j])
        {
            if S[i] != S[N/2 + i] {
                isConcat := false;
            }
            i := i + 1;
        }
        
        if isConcat {
            assert forall j :: 0 <= j < N/2 ==> S[j] == S[N/2 + j];
            assert IsConcatenationOfTwoCopies(S);
            result := "Yes";
        } else {
            assert !(forall j :: 0 <= j < N/2 ==> S[j] == S[N/2 + j]);
            assert !IsConcatenationOfTwoCopies(S);
            result := "No";
        }
    }
}
// </vc-code>

