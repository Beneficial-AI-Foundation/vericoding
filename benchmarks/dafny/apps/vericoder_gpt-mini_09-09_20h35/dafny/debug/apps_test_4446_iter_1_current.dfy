predicate ValidInput(n: int, a: int, b: int, k: int, H: seq<int>)
{
    n > 0 && a > 0 && b > 0 && k >= 0 && |H| == n && 
    forall i :: 0 <= i < |H| ==> H[i] > 0
}

function ProcessHealthValues(H: seq<int>, a: int, b: int): seq<int>
    requires a > 0 && b > 0
    requires forall i :: 0 <= i < |H| ==> H[i] > 0
    ensures |ProcessHealthValues(H, a, b)| == |H|
    ensures forall i :: 0 <= i < |H| ==> 
        var h_mod := H[i] % (a + b);
        ProcessHealthValues(H, a, b)[i] == (if h_mod == 0 then a + b else h_mod)
    ensures forall i :: 0 <= i < |ProcessHealthValues(H, a, b)| ==> 
        1 <= ProcessHealthValues(H, a, b)[i] <= a + b
{
    if |H| == 0 then []
    else 
        var h_mod := H[0] % (a + b);
        var h_final := if h_mod == 0 then a + b else h_mod;
        [h_final] + ProcessHealthValues(H[1..], a, b)
}

function CountKillableMonsters(sorted_health: seq<int>, a: int, k: int): int
    requires a > 0 && k >= 0
    requires forall i, j :: 0 <= i < j < |sorted_health| ==> sorted_health[i] <= sorted_health[j]
    requires forall i :: 0 <= i < |sorted_health| ==> sorted_health[i] > 0
    ensures 0 <= CountKillableMonsters(sorted_health, a, k) <= |sorted_health|
{
    CountKillableHelper(sorted_health, a, k, 0, 0)
}

function CountKillableHelper(sorted_health: seq<int>, a: int, remaining_k: int, index: int, acc: int): int
    requires a > 0 && remaining_k >= 0 && 0 <= index <= |sorted_health| && acc >= 0
    requires forall i, j :: 0 <= i < j < |sorted_health| ==> sorted_health[i] <= sorted_health[j]
    requires forall i :: 0 <= i < |sorted_health| ==> sorted_health[i] > 0
    ensures CountKillableHelper(sorted_health, a, remaining_k, index, acc) >= acc
    ensures CountKillableHelper(sorted_health, a, remaining_k, index, acc) <= acc + (|sorted_health| - index)
    decreases |sorted_health| - index
{
    if index >= |sorted_health| then acc
    else
        var x := sorted_health[index];
        if x <= a then
            CountKillableHelper(sorted_health, a, remaining_k, index + 1, acc + 1)
        else
            var needed_skips := (x + a - 1) / a - 1;
            if remaining_k >= needed_skips then
                CountKillableHelper(sorted_health, a, remaining_k - needed_skips, index + 1, acc + 1)
            else
                CountKillableHelper(sorted_health, a, remaining_k, index + 1, acc)
}

// <vc-helpers>
method SortSequence(H: seq<int>) returns (res: seq<int>)
    requires forall i :: 0 <= i < |H| ==> H[i] > 0
    ensures multiset(res) == multiset(H)
    ensures forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
    decreases |H|
{
    if |H| == 0 {
        res := [];
        return;
    }

    // Find minimal element and its index
    var min := H[0];
    var minIdx := 0;
    var i := 1;
    while i < |H|
        invariant 1 <= |H|
        invariant 1 <= i <= |H|
        invariant 0 <= minIdx < |H|
        invariant forall t :: 0 <= t < i ==> min <= H[t]
        decreases |H| - i
    {
        if H[i] < min {
            min := H[i];
            minIdx := i;
        }
        i := i + 1;
    }

    // Remove the minimal element and sort the rest
    var rest := H[..minIdx] + H[minIdx+1..];
    var sorted_rest := SortSequence(rest);

    // min is <= every element of rest, hence <= every element of sorted_rest
    assert forall j :: 0 <= j < |rest| ==> min <= rest[j];
    // From multiset equality of sorted_rest and rest, elements of sorted_rest satisfy same property
    assert multiset(sorted_rest) == multiset(rest);
    assert forall j :: 0 <= j < |sorted_rest| ==> min <= sorted_rest[j];

    // Combine
    res := [min] + sorted_rest;

    // Prove multiset equality
    assert multiset([min] + sorted_rest) == multiset([min]) + multiset(sorted_rest);
    assert multiset(rest) + multiset([min]) == multiset(H);
    assert multiset(sorted_rest) == multiset(rest);
    assert multiset(res) == multiset(H);

    // Prove sortedness
    // For indices within sorted_rest, order holds by recursion
    assert forall i1, i2 :: 1 <= i1 < i2 < |res| ==> res[i1] <= res[i2];
    // For index 0 compared to others: min <= sorted_rest[j] holds from above
    assert forall j :: 1 <= j < |res| ==> res[0] <= res[j];
}
// </vc-helpers>

// <vc-spec>
method SolveCore(n: int, a: int, b: int, k: int, H: seq<int>) returns (result: int)
    requires ValidInput(n, a, b, k, H)
    ensures 0 <= result <= n
// </vc-spec>
// <vc-code>
{
    var processed := ProcessHealthValues(H, a, b);
    var sorted := SortSequence(processed);
    result := CountKillableMonsters(sorted, a, k);
}
// </vc-code>

