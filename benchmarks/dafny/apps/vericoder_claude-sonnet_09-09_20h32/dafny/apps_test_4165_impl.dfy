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
    ensures multiset(filter(s, pred)) <= multiset(s)
    decreases |s|
{
    if |s| == 0 {
        assert filter(s, pred) == [];
        assert multiset([]) <= multiset(s);
    } else if pred(s[0]) {
        var rest := filter(s[1..], pred);
        filterPreservesInclusion(s[1..], pred);
        assert multiset(rest) <= multiset(s[1..]);
        assert filter(s, pred) == [s[0]] + rest;
        assert multiset([s[0]] + rest) == multiset([s[0]]) + multiset(rest);
        assert multiset([s[0]]) + multiset(rest) <= multiset([s[0]]) + multiset(s[1..]);
        assert s == [s[0]] + s[1..];
        assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
    } else {
        var rest := filter(s[1..], pred);
        filterPreservesInclusion(s[1..], pred);
        assert filter(s, pred) == rest;
        assert multiset(rest) <= multiset(s[1..]);
        assert s == [s[0]] + s[1..];
        assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
        assert multiset(s[1..]) <= multiset(s);
    }
}

lemma partitionMultisetHelper(s: seq<int>, pivot: int)
    ensures multiset(s) == multiset(filter(s, x => x < pivot)) + 
                          multiset(filter(s, x => x == pivot)) + 
                          multiset(filter(s, x => x > pivot))
    decreases |s|
{
    if |s| == 0 {
        assert filter(s, x => x < pivot) == [];
        assert filter(s, x => x == pivot) == [];
        assert filter(s, x => x > pivot) == [];
    } else {
        var head := s[0];
        var tail := s[1..];
        partitionMultisetHelper(tail, pivot);
        
        var left_tail := filter(tail, x => x < pivot);
        var equal_tail := filter(tail, x => x == pivot);
        var right_tail := filter(tail, x => x > pivot);
        
        assert multiset(tail) == multiset(left_tail) + multiset(equal_tail) + multiset(right_tail);
        assert s == [head] + tail;
        assert multiset(s) == multiset([head]) + multiset(tail);
        
        if head < pivot {
            assert filter(s, x => x < pivot) == [head] + left_tail;
            assert filter(s, x => x == pivot) == equal_tail;
            assert filter(s, x => x > pivot) == right_tail;
            assert multiset(filter(s, x => x < pivot)) == multiset([head]) + multiset(left_tail);
        } else if head == pivot {
            assert filter(s, x => x < pivot) == left_tail;
            assert filter(s, x => x == pivot) == [head] + equal_tail;
            assert filter(s, x => x > pivot) == right_tail;
            assert multiset(filter(s, x => x == pivot)) == multiset([head]) + multiset(equal_tail);
        } else {
            assert filter(s, x => x < pivot) == left_tail;
            assert filter(s, x => x == pivot) == equal_tail;
            assert filter(s, x => x > pivot) == [head] + right_tail;
            assert multiset(filter(s, x => x > pivot)) == multiset([head]) + multiset(right_tail);
        }
    }
}

lemma partitionPreservesMultiset(s: seq<int>, pivot: int)
    requires |s| > 0
    ensures var left := filter(s[1..], x => x < pivot);
            var equal := filter(s, x => x == pivot);
            var right := filter(s[1..], x => x > pivot);
            multiset(s) == multiset(left) + multiset(equal) + multiset(right)
{
    var left := filter(s[1..], x => x < pivot);
    var equal := filter(s, x => x == pivot);
    var right := filter(s[1..], x => x > pivot);
    
    assert s == [s[0]] + s[1..];
    assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
    
    partitionMultisetHelper(s[1..], pivot);
    
    var left_tail := filter(s[1..], x => x < pivot);
    var equal_tail := filter(s[1..], x => x == pivot);
    var right_tail := filter(s[1..], x => x > pivot);
    
    assert multiset(s[1..]) == multiset(left_tail) + multiset(equal_tail) + multiset(right_tail);
    assert left == left_tail;
    assert right == right_tail;
    
    if s[0] < pivot {
        assert s[0] !in filter(s, x => x == pivot);
        assert equal == equal_tail;
        assert multiset([s[0]]) + multiset(left_tail) == multiset(left);
        assert multiset([s[0]]) + multiset(s[1..]) == multiset([s[0]]) + multiset(left_tail) + multiset(equal_tail) + multiset(right_tail);
        assert multiset(s) == multiset(left) + multiset(equal) + multiset(right);
    } else if s[0] == pivot {
        assert s[0] in filter(s, x => x == pivot);
        assert equal == [s[0]] + equal_tail;
        assert multiset(equal) == multiset([s[0]]) + multiset(equal_tail);
        assert multiset([s[0]]) + multiset(s[1..]) == multiset(left) + multiset([s[0]]) + multiset(equal_tail) + multiset(right);
        assert multiset(s) == multiset(left) + multiset(equal) + multiset(right);
    } else {
        assert s[0] !in filter(s, x => x == pivot);
        assert equal == equal_tail;
        assert multiset([s[0]]) + multiset(right_tail) == multiset(right);
        assert multiset([s[0]]) + multiset(s[1..]) == multiset(left_tail) + multiset(equal_tail) + multiset([s[0]]) + multiset(right_tail);
        assert multiset(s) == multiset(left) + multiset(equal) + multiset(right);
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
    var sortedSides := quicksort(sides);
    var longest := sortedSides[|sortedSides|-1];
    var sumOfOthers := sumExceptLast(sortedSides);
    
    if sumOfOthers > longest {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

