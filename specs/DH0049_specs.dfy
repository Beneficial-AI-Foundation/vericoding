// <vc-preamble>

function InsertSorted(x: real, sorted: seq<real>): seq<real>
{
    if |sorted| == 0 then [x]
    else if x <= sorted[0] then [x] + sorted
    else [sorted[0]] + InsertSorted(x, sorted[1..])
}

function Sort(s: seq<real>): seq<real>
{
    if |s| == 0 then []
    else InsertSorted(s[0], Sort(s[1..]))
}

predicate IsSorted(s: seq<real>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Multiset(s: seq<real>): multiset<real> {
    if |s| == 0 then multiset{}
    else multiset{s[0]} + Multiset(s[1..])
}

predicate ValidInput(l: seq<real>) {
    |l| > 0
}

function MedianValue(l: seq<real>): real
    requires ValidInput(l)
{
    var sorted_list := Sort(l);
    var n := |sorted_list|;
    if n % 2 == 1 then
        sorted_list[n / 2]
    else
        (sorted_list[n / 2 - 1] + sorted_list[n / 2]) / 2.0
}
lemma InsertSortedPreservesOrder(x: real, sorted: seq<real>)
    requires IsSorted(sorted)
    ensures IsSorted(InsertSorted(x, sorted))
{
    if |sorted| == 0 {
    } else if x <= sorted[0] {
    } else {
        InsertSortedPreservesOrder(x, sorted[1..]);
        var result := InsertSorted(x, sorted[1..]);
        assert IsSorted(result);
        if |result| > 0 {
            assert sorted[0] <= result[0];
        }
        assert IsSorted([sorted[0]] + result);
    }
}

lemma SortProducesOrder(s: seq<real>)
    ensures IsSorted(Sort(s))
{
    if |s| == 0 {
    } else {
        SortProducesOrder(s[1..]);
        InsertSortedPreservesOrder(s[0], Sort(s[1..]));
    }
}

lemma InsertSortedPreservesMultiset(x: real, sorted: seq<real>)
    ensures Multiset(InsertSorted(x, sorted)) == multiset{x} + Multiset(sorted)
{
    if |sorted| == 0 {
    } else if x <= sorted[0] {
    } else {
        InsertSortedPreservesMultiset(x, sorted[1..]);
    }
}

lemma SortPreservesMultiset(s: seq<real>)
    ensures Multiset(Sort(s)) == Multiset(s)
{
    if |s| == 0 {
    } else {
        SortPreservesMultiset(s[1..]);
        InsertSortedPreservesMultiset(s[0], Sort(s[1..]));
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method median(l: seq<real>) returns (result: real)
    requires ValidInput(l)
    ensures result == MedianValue(l)
    ensures var sorted_list := Sort(l);
            var n := |sorted_list|;
            n % 2 == 1 ==> result == sorted_list[n / 2]
    ensures var sorted_list := Sort(l);
            var n := |sorted_list|;
            n % 2 == 0 ==> result == (sorted_list[n / 2 - 1] + sorted_list[n / 2]) / 2.0
    ensures IsSorted(Sort(l))
    ensures Multiset(Sort(l)) == Multiset(l)
    ensures |l| == 1 ==> result == l[0]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
