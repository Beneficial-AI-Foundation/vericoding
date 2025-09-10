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
lemma NoRepeatsEquivalence(words: seq<string>)
    ensures NoRepeats(words) <==> (forall i, j :: 0 <= i < j < |words| ==> words[i] != words[j])
{
}

lemma ConsecutiveCharsMatchEquivalence(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
    ensures ConsecutiveCharsMatch(words) <==> (forall i :: 0 <= i < |words| - 1 ==> words[i][|words[i]| - 1] == words[i+1][0])
{
}

lemma ValidShiritoriEquivalence(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
    ensures ValidShiritori(words) <==> (NoRepeats(words) && ConsecutiveCharsMatch(words))
{
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
    var hasNoRepeats := true;
    var i := 0;
    while i < |words| && hasNoRepeats
        invariant 0 <= i <= |words|
        invariant hasNoRepeats <==> (forall x, y :: 0 <= x < y < i ==> words[x] != words[y])
    {
        var j := i + 1;
        while j < |words| && hasNoRepeats
            invariant i + 1 <= j <= |words|
            invariant hasNoRepeats <==> (forall x, y :: 0 <= x < y < i ==> words[x] != words[y]) && (forall k :: i + 1 <= k < j ==> words[i] != words[k])
        {
            if words[i] == words[j] {
                hasNoRepeats := false;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    var consecutiveMatch := true;
    var k := 0;
    while k < |words| - 1 && consecutiveMatch
        invariant 0 <= k <= |words| - 1
        invariant consecutiveMatch <==> (forall idx :: 0 <= idx < k ==> words[idx][|words[idx]| - 1] == words[idx + 1][0])
    {
        if words[k][|words[k]| - 1] != words[k + 1][0] {
            consecutiveMatch := false;
        }
        k := k + 1;
    }
    
    if hasNoRepeats && consecutiveMatch {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

