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
lemma ValidInputImpliesEvenLength(S: string)
    requires ValidInput(S)
    ensures |S| % 2 == 0
{
}

lemma ValidInputIsEvenString(S: string)
    requires ValidInput(S)
    ensures IsEvenString(S)
{
}

lemma ValidInputHasSolution(S: string)
    requires ValidInput(S)
    ensures ValidSolution(S, |S|)
{
    ValidInputImpliesEvenLength(S);
    ValidInputIsEvenString(S);
}

lemma SolutionExists(S: string)
    requires ValidInput(S)
    ensures exists k :: ValidSolution(S, k)
{
    ValidInputHasSolution(S);
}

lemma ValidSolutionBounds(S: string, k: int)
    requires ValidInput(S)
    requires k >= 2 && k <= |S| && k % 2 == 0
    requires IsEvenString(S[..k])
    ensures ValidSolution(S, k)
{
}

lemma FullStringSolution(S: string)
    requires ValidInput(S)
    ensures ValidSolution(S, |S|)
{
    ValidInputHasSolution(S);
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
    FullStringSolution(S);
    
    var k := |S|;
    while k > 2
        invariant k >= 2
        invariant k <= |S|
        invariant k % 2 == 0
        invariant forall j :: k < j <= |S| && j % 2 == 0 ==> !IsEvenString(S[..j])
        invariant ValidSolution(S, |S|)
        decreases k
    {
        if IsEvenString(S[..k]) {
            ValidSolutionBounds(S, k);
            result := k;
            return;
        }
        k := k - 2;
    }
    
    // k == 2, return the full string since it's guaranteed to be a valid solution
    result := |S|;
}
// </vc-code>

