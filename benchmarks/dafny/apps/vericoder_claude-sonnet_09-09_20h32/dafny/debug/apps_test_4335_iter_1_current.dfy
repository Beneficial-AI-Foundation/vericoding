predicate ValidInput(N: int, S: string)
{
    1 <= N <= 100 && |S| == N && forall i :: 0 <= i < |S| ==> 'a' <= S[i] <= 'z'
}

predicate IsConcatenationOfTwoCopies(S: string)
{
    |S| % 2 == 0 && forall i :: 0 <= i < |S|/2 ==> S[i] == S[|S|/2 + i]
}

// <vc-helpers>
lemma EvenLengthImpliesEvenN(N: int, S: string)
    requires ValidInput(N, S)
    requires N % 2 == 0
    ensures |S| % 2 == 0
{
    assert |S| == N;
}

lemma OddLengthImpliesNotConcatenation(S: string)
    requires |S| % 2 != 0
    ensures !IsConcatenationOfTwoCopies(S)
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
        EvenLengthImpliesEvenN(N, S);
        var halfLength := N / 2;
        var isConcat := true;
        var i := 0;
        while i < halfLength
            invariant 0 <= i <= halfLength
            invariant isConcat <==> (forall j :: 0 <= j < i ==> S[j] == S[halfLength + j])
        {
            if S[i] != S[halfLength + i] {
                isConcat := false;
                break;
            }
            i := i + 1;
        }
        
        if isConcat {
            result := "Yes";
        } else {
            result := "No";
        }
    }
}
// </vc-code>

