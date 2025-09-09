Given a string representing a row of cells with flowers (A, B, C) or empty cells (.),
determine if it's possible for at least one cell to contain all three colors after
some flowers wither and spread petals to adjacent cells.

predicate ValidInput(s: string)
{
    |s| >= 0 && forall i :: 0 <= i < |s| ==> s[i] in {'A', 'B', 'C', '.'}
}

predicate HasAllThreeColors(s: string, start: int)
    requires 0 <= start <= |s| - 3
{
    'A' in s[start..start+3] && 'B' in s[start..start+3] && 'C' in s[start..start+3]
}

predicate PossibleToGetAllColors(s: string)
{
    |s| >= 3 && exists i :: 0 <= i <= |s| - 3 && HasAllThreeColors(s, i)
}

method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" ==> PossibleToGetAllColors(s)
    ensures result == "No" ==> !PossibleToGetAllColors(s)
    ensures result == "Yes" || result == "No"
{
    var n := |s|;

    if n < 3 {
        result := "No";
        return;
    }

    var possible := false;
    var witnessIndex := -1;

    var i := 0;
    while i <= n - 3
        invariant 0 <= i <= n - 2
        invariant !possible ==> (forall k :: 0 <= k < i ==> !HasAllThreeColors(s, k))
        invariant possible ==> (0 <= witnessIndex < i && HasAllThreeColors(s, witnessIndex))
    {
        var hasA := false;
        var hasB := false;
        var hasC := false;

        var j := i;
        while j < i + 3
            invariant i <= j <= i + 3
            invariant hasA ==> 'A' in s[i..j]
            invariant hasB ==> 'B' in s[i..j]  
            invariant hasC ==> 'C' in s[i..j]
            invariant !hasA ==> 'A' !in s[i..j]
            invariant !hasB ==> 'B' !in s[i..j]
            invariant !hasC ==> 'C' !in s[i..j]
        {
            if s[j] == 'A' {
                hasA := true;
            } else if s[j] == 'B' {
                hasB := true;
            } else if s[j] == 'C' {
                hasC := true;
            }
            j := j + 1;
        }

        assert hasA && hasB && hasC <==> HasAllThreeColors(s, i);

        if hasA && hasB && hasC {
            possible := true;
            witnessIndex := i;
            break;
        }
        i := i + 1;
    }

    if possible {
        result := "Yes";
    } else {
        assert forall k :: 0 <= k <= n - 3 ==> !HasAllThreeColors(s, k);
        result := "No";
    }
}
