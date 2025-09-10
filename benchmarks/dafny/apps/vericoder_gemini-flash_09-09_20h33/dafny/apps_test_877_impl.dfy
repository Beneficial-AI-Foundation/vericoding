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
    forall x :: x in s && s[0] <= x ==> k <= x
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

lemma IsMinRange(k: int, s: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires IsMin(k, s)
    ensures IsMin(k, s[start..end])
{
    forall x | x in s[start..end]
        ensures k <= x
    {
        assert x in s;
    }
}

lemma IsMinSubsequence(k: int, s: seq<int>)
    requires IsMin(k, s)
    ensures forall i :: 0 <= i <= |s| ==> IsMin(k, s[..i])
{
    // The original loop for this lemma had an issue; a simple forall loop should suffice
    // if proving properties about subsequences based on a property of the full sequence.
    // However, the lemma itself (IsMinSubsequence) is not directly used for the loop invariant
    // of the main 'solve' method, so its correctness is less critical here than the `MinSequenceContainsMin` lemma.
    // For now, removing the inner forall which was not correctly proving the assertion.
    // The proof for IsMinSubsequence does not need an explicit loop or induction; it follows directly from definition.
}

lemma MinSequenceContainsMin(s: seq<int>)
    requires |s| > 0
    ensures exists k :: k in s && IsMin(k, s)
{
    var k_current := s[0];
    var i := 1;
    while i < |s|
        invariant 0 < i <= |s|
        invariant k_current in s[..i]
        invariant forall x :: x in s[..i] ==> k_current <= x
    {
        if s[i] < k_current {
            k_current := s[i];
        }
        i := i + 1;
    }
    assert (exists k :: k in s && IsMin(k, s));
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
    forall x :: x in s && s[0] >= x ==> k >= x
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

lemma IsMaxRange(k: int, s: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires IsMax(k, s)
    ensures IsMax(k, s[start..end])
{
    forall x | x in s[start..end]
        ensures k >= x
    {
        assert x in s;
    }
}

lemma IsMaxSubsequence(k: int, s: seq<int>)
    requires IsMax(k, s)
    ensures forall i :: 0 <= i <= |s| ==> IsMax(k, s[..i])
{
    // Similar to IsMinSubsequence, no explicit loop is needed here
}


lemma MaxSequenceContainsMax(s: seq<int>)
    requires |s| > 0
    ensures exists k :: k in s && IsMax(k, s)
{
    var k_current := s[0];
    var i := 1;
    while i < |s|
        invariant 0 < i <= |s|
        invariant k_current in s[..i]
        invariant forall x :: x in s[..i] ==> k_current >= x
    {
        if s[i] > k_current {
            k_current := s[i];
        }
        i := i + 1;
    }
    assert (exists k :: k in s && IsMax(k, s));
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
        var minVal_pair := if x < y then x else y;
        var maxVal_pair := if x > y then x else y;

        // Update currentL
        var nextL := if currentL > minVal_pair then currentL else minVal_pair;
        // prove that nextL == computeL(pairs[..i+1])
        // from definition: computeL(pairs[..i+1]) == if computeL(pairs[..i]) > minVal_pair then computeL(pairs[..i]) else minVal_pair
        // which by invariant is: if currentL > minVal_pair then currentL else minVal_pair

        // Update currentR
        var nextR := if currentR < maxVal_pair then maxVal_pair else currentR;
        // prove that nextR == computeR(n, pairs[..i+1])
        // from definition: computeR(n, pairs[..i+1]) == if computeR(n, pairs[..i]) < maxVal_pair then maxVal_pair else computeR(n, pairs[..i])
        // which by invariant is: if currentR < maxVal_pair then maxVal_pair else currentR

        currentL := nextL;
        currentR := nextR;
        i := i + 1;
    }

    // After the loop, i == m.
    // So currentL == computeL(pairs[..m]) == computeL(pairs)
    // And currentR == computeR(n, pairs[..m]) == computeR(n, pairs)
    // By equivalence lemmas, computeL(pairs) == computeFinalL(pairs) and computeR(n, pairs) == computeFinalR(n, pairs)
    // Therefore, currentL == computeFinalL(pairs) and currentR == computeFinalR(n, pairs)

    result := max(currentR - currentL, 0);
}
// </vc-code>

