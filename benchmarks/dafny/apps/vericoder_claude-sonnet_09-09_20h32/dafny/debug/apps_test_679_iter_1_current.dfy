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

// <vc-helpers>
lemma HasAllThreeColorsCharacterization(s: string, start: int)
    requires 0 <= start <= |s| - 3
    ensures HasAllThreeColors(s, start) <==> 
        ('A' in s[start..start+3] && 'B' in s[start..start+3] && 'C' in s[start..start+3])
{
}

lemma PossibleToGetAllColorsEquivalence(s: string)
    ensures PossibleToGetAllColors(s) <==> 
        (|s| >= 3 && exists i :: 0 <= i <= |s| - 3 && HasAllThreeColors(s, i))
{
}

lemma NotPossibleToGetAllColorsCharacterization(s: string)
    ensures !PossibleToGetAllColors(s) <==> 
        (|s| < 3 || forall i :: 0 <= i <= |s| - 3 ==> !HasAllThreeColors(s, i))
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" ==> PossibleToGetAllColors(s)
    ensures result == "No" ==> !PossibleToGetAllColors(s)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
    if |s| < 3 {
        result := "No";
        return;
    }
    
    var i := 0;
    while i <= |s| - 3
        invariant 0 <= i <= |s| - 3 + 1
        invariant forall j :: 0 <= j < i ==> !HasAllThreeColors(s, j)
    {
        var hasA := 'A' in s[i..i+3];
        var hasB := 'B' in s[i..i+3];
        var hasC := 'C' in s[i..i+3];
        
        if hasA && hasB && hasC {
            result := "Yes";
            return;
        }
        
        i := i + 1;
    }
    
    result := "No";
}
// </vc-code>

