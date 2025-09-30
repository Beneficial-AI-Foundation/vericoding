predicate IsEvenString(s: string)
{
    |s| >= 2 && |s| % 2 == 0 && s[..|s|/2] == s[|s|/2..]
}

predicate ValidInput(S: string)
{
    |S| >= 2 && IsEvenString(S)
}

predicate ValidSolution(S: string, result: int)
{
    2 <= result < |S| && result % 2 == 0 && IsEvenString(S[..result])
}

predicate IsMaximalSolution(S: string, result: int)
{
    ValidSolution(S, result) && 
    forall k :: result < k < |S| && k % 2 == 0 ==> !IsEvenString(S[..k])
}

// <vc-helpers>
lemma ValidSolutionExists(S: string, k: int)
    requires ValidInput(S)
    requires ValidSolution(S, k)
    ensures exists j :: ValidSolution(S, j)
{
    assert ValidSolution(S, k);
}

lemma EvenStringPrefix(S: string, k: int)
    requires ValidInput(S)
    requires 2 <= k <= |S|
    requires k % 2 == 0
    requires S[..k/2] == S[k/2..k]
    ensures IsEvenString(S[..k])
{
    var prefix := S[..k];
    assert |prefix| == k;
    assert prefix[..|prefix|/2] == S[..k/2];
    assert prefix[|prefix|/2..] == S[k/2..k];
}
// </vc-helpers>

// <vc-spec>
method solve(S: string) returns (result: int)
    requires ValidInput(S)
    requires exists k :: ValidSolution(S, k)
    ensures ValidSolution(S, result)
    ensures IsMaximalSolution(S, result)
// </vc-spec>
// <vc-code>
{
    result := if |S| % 2 == 0 then |S| - 2 else |S| - 1;
    
    while result >= 2
        invariant result % 2 == 0
        invariant 0 <= result < |S|
        invariant forall k :: result < k < |S| && k % 2 == 0 ==> !IsEvenString(S[..k])
        decreases result
    {
        if S[..result/2] == S[result/2..result] {
            EvenStringPrefix(S, result);
            assert IsEvenString(S[..result]);
            assert ValidSolution(S, result);
            return;
        }
        result := result - 2;
    }
    
    // This point should be unreachable due to precondition
    assert false;
}
// </vc-code>

