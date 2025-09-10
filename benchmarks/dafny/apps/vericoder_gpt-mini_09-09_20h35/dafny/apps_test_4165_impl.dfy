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
    ensures forall x :: x in multiset(filter(s, pred)) ==> pred(x)
    ensures multiset(filter(s, pred)) <= multiset(s)
{
    if |s| == 0 {
        // filter([]) == []
        assert filter(s, pred) == [];
        assert multiset(filter(s, pred)) == multiset([]);
    } else {
        if pred(s[0]) {
            // By the definition of filter, when pred(s[0]) is true:
            // filter(s, pred) == [s[0]] + filter(s[1..], pred)
            var rest := filter(s[1..], pred);
            assert filter(s, pred) == [s[0]] + rest;

            // Use induction on the tail
            filterPreservesInclusion(s[1..], pred);

            // multiset([s[0]] + rest) == multiset([s[0]]) + multiset(rest)
            assert multiset(filter(s, pred)) == multiset([s[0]]) + multiset(rest);
            // rest elements are from s[1..], so multiset(rest) <= multiset(s[1..])
            assert multiset(rest) <= multiset(s[1..]);
            // multiset([s[0]]) + multiset(s[1..]) == multiset(s)
            assert multiset([s[0]]) + multiset(s[1..]) == multiset(s);
            // hence multiset(filter(s,pred)) <= multiset(s)
            assert multiset(filter(s, pred)) <= multiset(s);

            // For pred property: s[0] satisfies pred, and by induction all elements of rest satisfy pred
            assert pred(s[0]);
            // The recursive call gives: forall x :: x in multiset(rest) ==> pred(x)
        } else {
            // By the definition of filter, when pred(s[0]) is false:
            // filter(s, pred) == filter(s[1..], pred)
            var rest := filter(s[1..], pred);
            assert filter(s, pred) == rest;

            // Use induction on the tail
            filterPreservesInclusion(s[1..], pred);

            // From induction multiset(rest) <= multiset(s[1..]) and multiset(s) == multiset([s[0]]) + multiset(s[1..])
            assert multiset(rest) <= multiset(s[1..]);
            assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
            assert multiset(rest) <= multiset(s);

            // pred(s[0]) is false, but all elements of rest satisfy pred by induction
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
  if canFormPolygon(sides) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

