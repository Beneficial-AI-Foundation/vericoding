predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n && forall i :: 0 <= i < |a| ==> a[i] >= 1
}

function Transform(a: seq<int>): seq<int>
{
    seq(|a|, i requires 0 <= i < |a| => a[i] - (i + 1))
}

function SumAbsDiffs(a: seq<int>, target: int): int
    ensures SumAbsDiffs(a, target) >= 0
{
    if |a| == 0 then 0
    else Abs(a[0] - target) + SumAbsDiffs(a[1..], target)
}

function MedianOf(a: seq<int>): int
{
    var sorted := SortedSeq(a);
    if |sorted| == 0 then 0
    else if |sorted| % 2 == 1 then
        sorted[|sorted| / 2]
    else if |sorted| == 2 then
        RoundToInt((sorted[0] as real + sorted[1] as real) / 2.0)
    else
        RoundToInt((sorted[|sorted| / 2 - 1] as real + sorted[|sorted| / 2] as real) / 2.0)
}

function SortedSeq(a: seq<int>): seq<int>
{
    a
}

function Abs(x: int): int
    ensures Abs(x) >= 0
{
    if x >= 0 then x else -x
}

function RoundToInt(x: real): int
{
    if x >= 0.0 then
        ((x + 0.5).Floor) as int
    else
        ((x - 0.5).Floor) as int
}

// <vc-helpers>
lemma SortedSeqProperties(a: seq<int>)
    ensures var s := SortedSeq(a); 
        |s| == |a| && multiset(s) == multiset(a)
    ensures forall i, j :: 0 <= i < j < |SortedSeq(a)| ==> SortedSeq(a)[i] <= SortedSeq(a)[j]
{
}

lemma TransformPreservesLength(a: seq<int>)
    ensures |Transform(a)| == |a|
{
}

lemma TransformPreservesMultiset(a: seq<int>)
    ensures multiset(Transform(a)) == multiset(seq(|a|, i requires 0 <= i < |a| => a[i] - (i + 1)))
{
}

lemma SumAbsDiffsProperties(a: seq<int>, target: int)
    decreases |a|
    ensures SumAbsDiffs(a, target) == sum i | 0 <= i < |a| :: Abs(a[i] - target)
{
    if |a| == 0 {
    } else {
        calc {
            SumAbsDiffs(a, target);
            == { assert |a| > 0; }
            Abs(a[0] - target) + SumAbsDiffs(a[1..], target);
            == { SumAbsDiffsProperties(a[1..], target); }
            Abs(a[0] - target) + sum i | 0 <= i < |a[1..]| :: Abs(a[1..][i] - target);
            == { assert |a[1..]| == |a| - 1; }
            Abs(a[0] - target) + sum i | 0 <= i < |a| - 1 :: Abs(a[i+1] - target);
            == { assert forall i | 0 <= i < |a| - 1 :: a[i+1] == a[i+1]; }
            sum i | 0 <= i < |a| :: Abs(a[i] - target);
        }
    }
}

lemma MedianMinimizesSumAbsDiffs(s: seq<int>)
    requires |s| > 0
    requires var sorted := SortedSeq(s); forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
}

lemma TransformTransformed(a: seq<int>)
    ensures var t := Transform(a);
        forall i :: 0 <= i < |a| ==> t[i] == a[i] - (i + 1)
{
}

lemma SumAbsDiffsEqualityHelper(a: seq<int>, target: int)
    ensures SumAbsDiffs(a, target) == sum i | 0 <= i < |a| :: Abs(a[i] - target)
{
    SumAbsDiffsProperties(a, target);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures result == SumAbsDiffs(Transform(a), MedianOf(Transform(a)))
// </vc-spec>
// <vc-code>
{
    var transformed := Transform(a);
    var median := MedianOf(transformed);
    
    TransformPreservesLength(a);
    SortedSeqProperties(transformed);
    SumAbsDiffsEqualityHelper(transformed, median);
    
    result := SumAbsDiffs(transformed, median);
}
// </vc-code>

