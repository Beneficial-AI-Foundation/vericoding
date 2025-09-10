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
lemma HasAllThreeColorsImpliesContains(s: string, start: int)
    requires 0 <= start <= |s| - 3
    requires HasAllThreeColors(s, start)
    ensures 'A' in s[start..start+3]
    ensures 'B' in s[start..start+3]
    ensures 'C' in s[start..start+3]
{
}

lemma NotPossibleIfNoPosition(s: string)
    requires |s| >= 3
    requires forall i :: 0 <= i <= |s| - 3 ==> !HasAllThreeColors(s, i)
    ensures !PossibleToGetAllColors(s)
{
}

lemma PossibleIfHasPosition(s: string, pos: int)
    requires 0 <= pos <= |s| - 3
    requires HasAllThreeColors(s, pos)
    ensures PossibleToGetAllColors(s)
{
}

lemma SubstringExtension(s: string, i: int, k: int, c: char)
    requires 0 <= i <= k < |s|
    ensures s[k] == c ==> c in s[i..k+1]
    ensures c in s[i..k] ==> c in s[i..k+1]
{
    if s[k] == c {
        assert s[i..k+1][k-i] == c;
    }
}

lemma UpdateCharPresence(s: string, i: int, k: int, c: char, hadChar: bool)
    requires 0 <= i <= k < |s|
    requires hadChar == (c in s[i..k])
    ensures (hadChar || s[k] == c) == (c in s[i..k+1])
{
    if s[k] == c {
        assert s[i..k+1][k-i] == c;
        assert c in s[i..k+1];
    } else if c in s[i..k] {
        assert c in s[i..k+1];
    }
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
        return "No";
    }
    
    var i := 0;
    while i <= |s| - 3
        invariant 0 <= i <= |s| - 2
        invariant forall j :: 0 <= j < i ==> !HasAllThreeColors(s, j)
    {
        var hasA := false;
        var hasB := false;
        var hasC := false;
        
        var k := i;
        while k < i + 3
            invariant i <= k <= i + 3
            invariant hasA == ('A' in s[i..k])
            invariant hasB == ('B' in s[i..k])
            invariant hasC == ('C' in s[i..k])
        {
            UpdateCharPresence(s, i, k, 'A', hasA);
            UpdateCharPresence(s, i, k, 'B', hasB);
            UpdateCharPresence(s, i, k, 'C', hasC);
            
            if s[k] == 'A' {
                hasA := true;
            } else if s[k] == 'B' {
                hasB := true;
            } else if s[k] == 'C' {
                hasC := true;
            }
            
            k := k + 1;
        }
        
        if hasA && hasB && hasC {
            assert HasAllThreeColors(s, i);
            PossibleIfHasPosition(s, i);
            return "Yes";
        }
        
        i := i + 1;
    }
    
    assert forall j :: 0 <= j <= |s| - 3 ==> !HasAllThreeColors(s, j);
    NotPossibleIfNoPosition(s);
    return "No";
}
// </vc-code>

