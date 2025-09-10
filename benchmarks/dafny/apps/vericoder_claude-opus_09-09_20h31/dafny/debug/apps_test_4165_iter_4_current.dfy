predicate ValidInput(sides: seq<int>)
{
    |sides| >= 3 && forall i :: 0 <= i < |sides| ==> sides[i] > 0
}

function canFormPolygon(sides: seq<int>): bool
    requires ValidInput(sides)
{
    var sortedSides := quicksort(sides);
    var longest := sortedSides[|sortedSides|-1];
    var sumOfOthers := sumExceptLast(sortedSides);
    sumOfOthers > longest
}

function quicksort(s: seq<int>): seq<int>
    ensures multiset(quicksort(s)) == multiset(s)
    ensures forall i, j :: 0 <= i <= j < |quicksort(s)| ==> quicksort(s)[i] <= quicksort(s)[j]
    decreases |s|
{
    if |s| <= 1 then s
    else
        var pivot := s[0];
        var left := filter(s[1..], x => x < pivot);
        var equal := filter(s, x => x == pivot);
        var right := filter(s[1..], x => x > pivot);

        assert s == [s[0]] + s[1..];
        assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
        assert s[0] == pivot;
        assert multiset([s[0]]) == multiset([pivot]);

        filterPreservesInclusion(s[1..], x => x < pivot);
        filterPreservesInclusion(s[1..], x => x == pivot);
        filterPreservesInclusion(s[1..], x => x > pivot);

        quicksort(left) + equal + quicksort(right)
}

function filter(s: seq<int>, pred: int -> bool): seq<int>
    ensures |filter(s, pred)| <= |s|
    ensures forall x :: x in multiset(filter(s, pred)) ==> x in multiset(s)
    ensures forall x :: x in multiset(filter(s, pred)) ==> pred(x)
    ensures multiset(filter(s, pred)) <= multiset(s)
    decreases |s|
{
    if |s| == 0 then []
    else if pred(s[0]) then 
        var rest := filter(s[1..], pred);
        assert s == [s[0]] + s[1..];
        assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
        assert multiset(rest) <= multiset(s[1..]);
        assert multiset([s[0]] + rest) == multiset([s[0]]) + multiset(rest);
        assert multiset([s[0]]) + multiset(rest) <= multiset([s[0]]) + multiset(s[1..]);
        [s[0]] + rest
    else 
        var rest := filter(s[1..], pred);
        assert multiset(rest) <= multiset(s[1..]);
        assert s == [s[0]] + s[1..];
        assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
        assert multiset(rest) <= multiset(s[1..]) <= multiset(s);
        rest
}

function sumExceptLast(s: seq<int>): int
    requires |s| >= 1
{
    if |s| == 1 then 0
    else s[0] + sumExceptLast(s[1..])
}

// <vc-helpers>
lemma filterPreservesInclusion(s: seq<int>, pred: int -> bool)
    ensures forall x :: x in multiset(filter(s, pred)) ==> x in multiset(s)
{
    if |s| == 0 {
        // Base case: empty sequence
    } else if pred(s[0]) {
        filterPreservesInclusion(s[1..], pred);
    } else {
        filterPreservesInclusion(s[1..], pred);
    }
}

function sumExceptLastCompute(s: seq<int>): int
    requires |s| >= 1
{
    sumExceptLast(s)
}

lemma sumExceptLastCorrect(s: seq<int>)
    requires |s| >= 2
    ensures sumExceptLast(s) == sumExceptLast(s[..|s|-1]) + s[|s|-2]
{
    if |s| == 2 {
        assert s[..|s|-1] == [s[0]];
        assert sumExceptLast(s) == s[0] + sumExceptLast(s[1..]);
        assert s[1..] == [s[1]];
        assert sumExceptLast(s[1..]) == 0;
        assert sumExceptLast(s) == s[0];
        assert sumExceptLast(s[..|s|-1]) == sumExceptLast([s[0]]) == 0;
        assert s[|s|-2] == s[0];
    } else {
        assert s == [s[0]] + s[1..];
        assert sumExceptLast(s) == s[0] + sumExceptLast(s[1..]);
        sumExceptLastCorrect(s[1..]);
    }
}

method quicksortMethod(s: seq<int>) returns (sorted: seq<int>)
    ensures multiset(sorted) == multiset(s)
    ensures forall i, j :: 0 <= i <= j < |sorted| ==> sorted[i] <= sorted[j]
    ensures sorted == quicksort(s)
{
    sorted := quicksort(s);
}

method computeSumExceptLast(s: seq<int>) returns (sum: int)
    requires |s| >= 1
    ensures sum == sumExceptLast(s)
{
    if |s| == 1 {
        sum := 0;
    } else {
        sum := 0;
        var i := 0;
        while i < |s| - 1
            invariant 0 <= i <= |s| - 1
            invariant sum == if i == 0 then 0 else sumExceptLast(s[..i+1])
        {
            sum := sum + s[i];
            i := i + 1;
            if i < |s| {
                assert s[..i] == s[..i-1] + [s[i-1]];
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(sides: seq<int>) returns (result: string)
    requires ValidInput(sides)
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> canFormPolygon(sides)
// </vc-spec>
// <vc-code>
{
    var sortedSides := quicksortMethod(sides);
    assert |sortedSides| == |sides| >= 3;
    var longest := sortedSides[|sortedSides|-1];
    var sumOfOthers := computeSumExceptLast(sortedSides);
    
    if sumOfOthers > longest {
        result := "Yes";
    } else {
        result := "No";
    }
    
    assert result == "Yes" <==> sumOfOthers > longest;
    assert sumOfOthers > longest <==> canFormPolygon(sides);
}
// </vc-code>

