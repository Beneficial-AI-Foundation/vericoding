predicate NoRepeats(words: seq<string>)
{
    forall i, j :: 0 <= i < j < |words| ==> words[i] != words[j]
}

predicate ConsecutiveCharsMatch(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
{
    forall i :: 0 <= i < |words| - 1 ==> words[i][|words[i]| - 1] == words[i+1][0]
}

predicate ValidShiritori(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
{
    NoRepeats(words) && ConsecutiveCharsMatch(words)
}

// <vc-helpers>
lemma NoRepeatsUpTo(words: seq<string>, k: int)
    requires 0 <= k <= |words|
    ensures NoRepeats(words[..k]) <==> (forall i, j :: 0 <= i < j < k ==> words[i] != words[j])
{
    assert words[..k] == words[..k];
}

lemma ConsecutiveCharsMatchUpTo(words: seq<string>, k: int)
    requires 0 <= k <= |words|
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
    ensures ConsecutiveCharsMatch(words[..k]) <==> (forall i :: 0 <= i < k - 1 ==> words[i][|words[i]| - 1] == words[i+1][0])
{
    if k > 0 {
        assert forall i :: 0 <= i < k ==> words[..k][i] == words[i];
    }
}
// </vc-helpers>

// <vc-spec>
method solve(words: seq<string>) returns (result: string)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> ValidShiritori(words)
// </vc-spec>
// <vc-code>
{
    // Check for no repeats
    var hasNoRepeats := true;
    var i := 0;
    while i < |words| && hasNoRepeats
        invariant 0 <= i <= |words|
        invariant hasNoRepeats <==> NoRepeats(words[..i])
    {
        var j := 0;
        while j < i && hasNoRepeats
            invariant 0 <= j <= i
            invariant hasNoRepeats <==> (NoRepeats(words[..i]) && forall k :: 0 <= k < j ==> words[k] != words[i])
        {
            if words[j] == words[i] {
                hasNoRepeats := false;
            }
            j := j + 1;
        }
        if hasNoRepeats {
            NoRepeatsUpTo(words, i + 1);
        }
        i := i + 1;
    }
    
    // Check consecutive character matching
    var consecutiveMatch := true;
    if |words| > 1 {
        i := 0;
        while i < |words| - 1 && consecutiveMatch
            invariant 0 <= i <= |words| - 1
            invariant consecutiveMatch <==> ConsecutiveCharsMatch(words[..i+1])
        {
            if words[i][|words[i]| - 1] != words[i+1][0] {
                consecutiveMatch := false;
            } else {
                ConsecutiveCharsMatchUpTo(words, i + 2);
            }
            i := i + 1;
        }
    }
    
    if hasNoRepeats && consecutiveMatch {
        assert NoRepeats(words[..|words|]);
        assert words[..|words|] == words;
        assert NoRepeats(words);
        
        if |words| > 0 {
            assert ConsecutiveCharsMatch(words[..|words|]);
            assert words[..|words|] == words;
            assert ConsecutiveCharsMatch(words);
        }
        
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

