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
lemma quicksortElementsPreserved(s: seq<int>)
    ensures forall x :: x in multiset(quicksort(s)) <==> x in multiset(s)
{
    // This property is directly ensured by the quicksort function (multiset(quicksort(s)) == multiset(s))
}

lemma filterMultiset(s: seq<int>, pred: int -> bool)
    ensures multiset(filter(s, pred)) <= multiset(s)
{
    if |s| == 0 {
        assert multiset([]) <= multiset([]);
    } else if pred(s[0]) {
        var rest := filter(s[1..], pred);
        assert multiset(rest) <= multiset(s[1..]);
        assert multiset([s[0]] + rest) == multiset([s[0]]) + multiset(rest);
        assert multiset([s[0]]) + multiset(rest) <= multiset([s[0]]) + multiset(s[1..]);
        assert multiset([s[0]]) + multiset(s[1..]) == multiset(s);
        assert multiset([s[0]] + rest) <= multiset(s);
    } else {
        var rest := filter(s[1..], pred);
        assert multiset(rest) <= multiset(s[1..]);
        assert multiset(s[1..]) <= multiset(s);
        assert multiset(rest) <= multiset(s);
    }
}

lemma filterProperties(s: seq<int>, pred: int -> bool)
    ensures (forall x :: x in multiset(filter(s, pred)) ==> pred(x))
    ensures (forall x :: x in multiset(filter(s, pred)) ==> x in multiset(s))
{
    if |s| > 0 {
        filterProperties(s[1..], pred);
        if pred(s[0]) {
            assert s[0] in multiset(filter(s, pred));
            assert pred(s[0]);
            assert s[0] in multiset(s);
        }
    }
}

lemma SumOfAllExceptLastIsSumMinusLast(s: seq<int>)
    requires |s| >= 1
    ensures sumExceptLast(s) == sum(s) - s[|s|-1]
    decreases |s|
{
    if |s| == 1 {
        calc {
            sumExceptLast(s);
            0;
            sum(s) - s[0];
            sum(s) - s[|s|-1];
        }
    } else {
        SumOfAllExceptLastIsSumMinusLast(s[1..]);
        calc {
            sumExceptLast(s);
            s[0] + sumExceptLast(s[1..]);
            s[0] + (sum(s[1..]) - s[|s|-1]);
            (s[0] + sum(s[1..])) - s[|s|-1];
            sum(s) - s[|s|-1];
        }
    }
}

function sum(s: seq<int>): int {
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}

lemma sumOfSortedPrefix(s: seq<int>, k: int)
    requires 0 <= k <= |s|
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures (sum(s[..k]) + s[k]) == sum(s[..k+1])
    decreases k
{
    if k > 0 {
        sumOfSortedPrefix(s, k-1);
    }
}

lemma sumElementsPositive(s: seq<int>)
    requires forall x :: x in multiset(s) ==> x > 0
    ensures |s| > 0 ==> sum(s) > 0
{
    if |s| > 0 {
        assert s[0] > 0;
        if |s| > 1 {
            sumElementsPositive(s[1..]);
            assert sum(s[1..]) > 0;
            assert sum(s) == s[0] + sum(s[1..]);
            assert sum(s) > 0;
        } else {
            assert sum(s) == s[0];
            assert sum(s) > 0;
        }
    }
}

lemma filterPreservesMultisetEquality(s: seq<int>, pred: int -> bool)
    ensures multiset(filter(s, pred)) <= multiset(s)
{
    filterMultiset(s, pred);
}

lemma filterPreservesInclusion(s: seq<int>, pred: int -> bool)
    ensures forall x :: x in multiset(filter(s, pred)) ==> x in multiset(s)
{
    filterProperties(s, pred);
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
    
    // Prove that the sorted sequence also contains only positive numbers
    quicksortElementsPreserved(sides);
    assert forall i :: 0 <= i < |sortedSides| ==> sortedSides[i] > 0
        by {
            forall i | 0 <= i < |sortedSides|
            ensures sortedSides[i] > 0 {
                assert sortedSides[i] in multiset(sortedSides);
                assert sortedSides[i] in multiset(sides); // From quicksortElementsPreserved
                // This implicitly relies on the fact that ValidInput ensures all elements in 'sides' are positive.
                // No explicit axiom needed, it's inferred from `quicksortElementsPreserved(sides);` and `ValidInput(sides)`
            }
        }

    // Prove that the last element is the largest
    // This is directly from the quicksort postcondition
    assert forall i :: 0 <= i < |sortedSides|-1 ==> sortedSides[i] <= sortedSides[|sortedSides|-1];

    var longest := sortedSides[|sortedSides|-1];

    // These `if` branches are unreachable because ValidInput ensures |sides| >= 3
    if |sortedSides| == 0 { 
        return "No";
    } else if |sortedSides| == 1 { 
        return "No";
    } else if |sortedSides| == 2 { 
        return "No";
    }

    var sumOfOthers := sumExceptLast(sortedSides);

    // Prove that sumOfOthers is sum(sortedSides[0..|sortedSides|-2])
    SumOfAllExceptLastIsSumMinusLast(sortedSides);
    assert sumOfOthers == sum(sortedSides) - longest;

    // Prove that sumOfOthers > 0
    if |sortedSides| > 1 { // This condition is always true given ValidInput
        assert forall x :: x in multiset(sortedSides[..|sortedSides|-1]) ==> x > 0
            by {
                forall x | x in multiset(sortedSides[..|sortedSides|-1])
                ensures x > 0 {
                    assert x in multiset(sortedSides); // x is part of the sorted sequence
                    // Since all elements in sortedSides are positive (proved above), x must be positive.
                }
            }
        sumElementsPositive(sortedSides[..|sortedSides|-1]);
    }
    assert sumOfOthers > 0; // Since |sides| >= 3, |sortedSides| >= 3, so its prefix (excluding the last element) has at least 2 elements, and all elements are positive.

    if sumOfOthers > longest {
        return "Yes";
    } else {
        return "No";
    }
}
// </vc-code>

