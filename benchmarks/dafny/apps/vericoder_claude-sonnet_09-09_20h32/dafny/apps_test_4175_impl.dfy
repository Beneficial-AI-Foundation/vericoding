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

lemma NoRepeatsHelper(words: seq<string>, i: int)
    requires 0 < i < |words|
    requires forall x, y :: 0 <= x < y < i ==> words[x] != words[y]
    requires forall k :: 0 <= k < i ==> words[k] != words[i]
    ensures forall x, y :: 0 <= x < y < i + 1 ==> words[x] != words[y]
{
    forall x, y | 0 <= x < y < i + 1
        ensures words[x] != words[y]
    {
        if y < i {
            assert words[x] != words[y];
        } else {
            assert y == i;
            assert x < i;
            assert words[x] != words[y];
        }
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
    if |words| == 0 {
        result := "Yes";
        return;
    }
    
    var hasNoRepeats := true;
    var i := 1;
    while i < |words| && hasNoRepeats
        invariant 1 <= i <= |words|
        invariant hasNoRepeats <==> (forall x, y :: 0 <= x < y < i ==> words[x] != words[y])
    {
        var j := 0;
        while j < i && hasNoRepeats
            invariant 0 <= j <= i
            invariant hasNoRepeats <==> (forall x, y :: 0 <= x < y < i ==> words[x] != words[y]) && (forall k :: 0 <= k < j ==> words[k] != words[i])
        {
            if words[j] == words[i] {
                hasNoRepeats := false;
            }
            j := j + 1;
        }
        if hasNoRepeats && i < |words| {
            NoRepeatsHelper(words, i);
        }
        i := i + 1;
    }
    
    var consecutiveMatch := true;
    if |words| > 1 {
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
    }
    
    if hasNoRepeats && consecutiveMatch {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

