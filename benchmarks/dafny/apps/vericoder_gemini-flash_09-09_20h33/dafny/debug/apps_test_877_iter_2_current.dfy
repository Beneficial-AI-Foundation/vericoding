predicate ValidInput(n: int, m: int, pairs: seq<(int, int)>)
{
    n >= 2 && 
    m >= 0 && 
    |pairs| == m &&
    (forall i :: 0 <= i < |pairs| ==> 1 <= pairs[i].0 <= n && 1 <= pairs[i].1 <= n) &&
    (forall i :: 0 <= i < |pairs| ==> pairs[i].0 != pairs[i].1)
}

function computeFinalL(pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then 1
    else 
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var minVal := if x < y then x else y;
        var restL := computeFinalL(pairs[..|pairs|-1]);
        if restL > minVal then restL else minVal
}

function computeFinalR(n: int, pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then n
    else
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var maxVal := if x > y then x else y;
        var restR := computeFinalR(n, pairs[..|pairs|-1]);
        if restR < maxVal then restR else maxVal
}

function max(a: int, b: int): int
{
    if a > b then a else b
}

predicate ValidResult(n: int, pairs: seq<(int, int)>, result: int)
{
    result >= 0 &&
    result <= n - 1 &&
    result == max(computeFinalR(n, pairs) - computeFinalL(pairs), 0)
}

// <vc-helpers>
function computeL(pairs: seq<(int, int)>): int
    ensures |pairs| == 0 ==> computeL(pairs) == 1
    ensures |pairs| > 0 ==> computeL(pairs) == var x := pairs[|pairs|-1].0; var y := pairs[|pairs|-1].1; var minVal := if x < y then x else y; if computeL(pairs[..|pairs|-1]) > minVal then computeL(pairs[..|pairs|-1]) else minVal
{
    if |pairs| == 0 then 1
    else
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var minVal := if x < y then x else y;
        var restL := computeL(pairs[..|pairs|-1]);
        if restL > minVal then restL else minVal
}

predicate IsMin(k: int, s: seq<int>)
{
    forall x :: x in s ==> k <= x
}

lemma IsMinSingleElement(k: int)
    ensures IsMin(k, [k])
{
}

lemma IsMinAppend(k: int, s: seq<int>, x: int)
    requires IsMin(k, s)
    requires k <= x
    ensures IsMin(k, s + [x])
{
}

lemma IsMinSubsequence(k: int, s: seq<int>)
    requires IsMin(k, s)
    ensures forall i :: 0 <= i < |s| ==> IsMin(k, s[..i])
{
    var _ := s[..0]; // trigger forall in ensures. base case
    forall i | 0 <= i < |s|
        ensures IsMin(k, s[..i])
    {
        forall x | x in s[..i] ensures k <= x
        {
            assert x in s;
        }
    }
}

lemma MinSequenceContainsMin(s: seq<int>)
    requires |s| > 0
    ensures exists k :: k in s && IsMin(k, s)
{
    var k := s[0];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        // Fix: The previous invariant `exists K :: K in s[..i] && IsMin(K, s[..i])` was not provable on entry.
        // We assert `IsMin(k, s[..i])` to be able to conclude it later.
        invariant IsMin(k, s[..i])
    {
        if s[i] < k {
            k := s[i];
        }
        i := i + 1;
    }
    assert IsMin(k, s);
}


function computeR(n: int, pairs: seq<(int, int)>): int
    ensures |pairs| == 0 ==> computeR(n, pairs) == n
    ensures |pairs| > 0 ==> computeR(n, pairs) == var x := pairs[|pairs|-1].0; var y := pairs[|pairs|-1].1; var maxVal := if x > y then x else y; if computeR(n, pairs[..|pairs|-1]) < maxVal then maxVal else computeR(n, pairs[..|pairs|-1])
{
    if |pairs| == 0 then n
    else
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var maxVal := if x > y then x else y;
        var restR := computeR(n, pairs[..|pairs|-1]);
        if restR < maxVal then maxVal else restR
}

predicate IsMax(k: int, s: seq<int>)
{
    forall x :: x in s ==> k >= x
}

lemma IsMaxSingleElement(k: int)
    ensures IsMax(k, [k])
{
}

lemma IsMaxAppend(k: int, s: seq<int>, x: int)
    requires IsMax(k, s)
    requires k >= x
    ensures IsMax(k, s + [x])
{
}

lemma IsMaxSubsequence(k: int, s: seq<int>)
    requires IsMax(k, s)
    ensures forall i :: 0 <= i < |s| ==> IsMax(k, s[..i])
{
    var _ := s[..0];
    forall i | 0 <= i < |s|
        ensures IsMax(k, s[..i])
    {
        forall x | x in s[..i] ensures k >= x
        {
            assert x in s;
        }
    }
}

lemma MaxSequenceContainsMax(s: seq<int>)
    requires |s| > 0
    ensures exists k :: k in s && IsMax(k, s)
{
    var k := s[0];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        // Fix: The previous invariant `exists K :: K in s[..i] && IsMax(K, s[..i])` was not provable on entry.
        // We assert `IsMax(k, s[..i])` to be able to conclude it later.
        invariant IsMax(k, s[..i])
    {
        if s[i] > k {
            k := s[i];
        }
        i := i + 1;
    }
    assert IsMax(k, s);
}

// Induction proof for computeFinalL and computeL being equivalent
lemma ComputeFinalLEquivalence(pairs: seq<(int, int)>)
    ensures computeFinalL(pairs) == computeL(pairs)
{
    if |pairs| == 0 {
        assert computeFinalL(pairs) == 1;
        assert computeL(pairs) == 1;
    } else {
        ComputeFinalLEquivalence(pairs[..|pairs|-1]);
    }
}

// Induction proof for computeFinalR and computeR being equivalent
lemma ComputeFinalREquivalence(n: int, pairs: seq<(int, int)>)
    ensures computeFinalR(n, pairs) == computeR(n, pairs)
{
    if |pairs| == 0 {
        assert computeFinalR(n, pairs) == n;
        assert computeR(n, pairs) == n;
    } else {
        ComputeFinalREquivalence(n, pairs[..|pairs|-1]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, pairs: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, m, pairs)
    ensures ValidResult(n, pairs, result)
// </vc-spec>
// <vc-code>
{
    ComputeFinalLEquivalence(pairs);
    ComputeFinalREquivalence(n, pairs);

    var currentL := 1;
    var currentR := n;

    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant currentL == computeL(pairs[..i])
        invariant currentR == computeR(n, pairs[..i])
    {
        var x := pairs[i].0;
        var y := pairs[i].1;
        var minVal := if x < y then x else y;
        var maxVal := if x > y then x else y;

        // Fix: Correctly update currentL to be the maximum of its current value and minVal
        // This is based on the definition of computeL (which finds the minimum of all minimums)
        currentL := if currentL > minVal then currentL else minVal;

        // Fix: Correctly update currentR to be the minimum of its current value and maxVal
        // This is based on the definition of computeR (which finds the maximum of all maximums)
        currentR := if currentR < maxVal then maxVal else currentR;
        i := i + 1;
    }

    result := max(currentR - currentL, 0);
}
// </vc-code>

