function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}
// pure-end
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
{
    // impl-start
    sorted := list;
    var i := 0;
    while i < |list|
        // invariants-start
        invariant 0 <= i <= |list|
        invariant |sorted| == |list|
        invariant multiset(sorted) == multiset(list)
        // invariants-end
    {
        var j := i + 1;
        var min := i;
        while j < |list|
            // invariants-start
            invariant 0 <= i <= j <= |list|
            invariant 0 <= min < j
            // invariants-end
        {
            if !comparison(sorted[min], sorted[j], 0) {
                min := j;
            }
            j := j + 1;
        }
        var temp := sorted[i];
        sorted := sorted[i := sorted[min]][min := temp];
        i := i + 1;
    }
    // impl-end
}

method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
    // impl-start
    sorted := list;
    var i := 0;
    while i < |list|
        // invariants-start
        invariant 0 <= i <= |list|
        invariant |sorted| == |list|
        invariant multiset(sorted) == multiset(list)
        invariant forall x :: 0 <= x < i ==> forall y :: i <= y < |sorted| ==> |sorted[x]| <= |sorted[y]|
        invariant forall x : int, y : int :: 0 <= x < y < i ==> |sorted[x]| <= |sorted[y]|
        invariant forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
        // invariants-end
    {
        var j := i + 1;
        var min := i;
        while j < |list|
            // invariants-start
            invariant 0 <= i < j <= |list|
            invariant i <= min < j
            invariant forall x :: i <= x < j ==> |sorted[min]| <= |sorted[x]|
            // invariants-end
        {
            if |sorted[j]| < |sorted[min]| {
                min := j;
            }
            j := j + 1;
        }
        var temp := sorted[i];
        sorted := sorted[i := sorted[min]][min := temp];
        i := i + 1;
    }
    // impl-end
}

method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
    // impl-start
    var init := sort_strings(list);

    sorted := [];
    var i := 0;

    while i < |init|
        // invariants-start
        invariant |init| > 0
        invariant multiset(init) == multiset(list)
        invariant 0 <= i <= |init|
        invariant |sorted| <= i
        invariant forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
        invariant multiset(sorted) <= multiset(init[0..i])
        // invariants-end
    {
        if |init[i]| % 2 == 0 {
            sorted := sorted + [init[i]];
            assert multiset(sorted) <= multiset(init[0..i + 1]); // assert-line
        } else {
            assert init[0..i + 1] == init[0..i] + [init[i]]; // assert-line
        }
        i := i + 1;
    }
    assert multiset(sorted) <= multiset(init[0..|init|]); // assert-line
    assert init[0..|init|] == init; // assert-line

    sorted := sort_lengths(sorted);
    // impl-end
}
