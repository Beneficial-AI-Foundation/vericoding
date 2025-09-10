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
function SortSeq(s: seq<int>): seq<int>
    ensures |SortSeq(s)| == |s|
    ensures multiset(SortSeq(s)) == multiset(s)
    ensures forall i, j :: 0 <= i < j < |SortSeq(s)| ==> SortSeq(s)[i] <= SortSeq(s)[j]

lemma ProcessHealthValuesPreservesPositive(H: seq<int>, a: int, b: int)
    requires a > 0 && b > 0
    requires forall i :: 0 <= i < |H| ==> H[i] > 0
    ensures var processed := ProcessHealthValues(H, a, b);
            forall i :: 0 <= i < |processed| ==> processed[i] > 0
{
    if |H| == 0 {
        return;
    }
    var h_mod := H[0] % (a + b);
    var h_final := if h_mod == 0 then a + b else h_mod;
    assert h_final > 0;
    ProcessHealthValuesPreservesPositive(H[1..], a, b);
}

lemma SortPreservesPositive(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] > 0
    ensures forall i :: 0 <= i < |SortSeq(s)| ==> SortSeq(s)[i] > 0
{
    assert multiset(SortSeq(s)) == multiset(s);
    forall i | 0 <= i < |SortSeq(s)|
        ensures SortSeq(s)[i] > 0
    {
        assert SortSeq(s)[i] in multiset(SortSeq(s));
        assert SortSeq(s)[i] in multiset(s);
        assert exists j :: 0 <= j < |s| && s[j] == SortSeq(s)[i];
    }
}
// </vc-helpers>

// <vc-spec>
method SolveCore(n: int, a: int, b: int, k: int, H: seq<int>) returns (result: int)
    requires ValidInput(n, a, b, k, H)
    ensures 0 <= result <= n
// </vc-spec>
// <vc-code>
{
    var processed_health := ProcessHealthValues(H, a, b);
    ProcessHealthValuesPreservesPositive(H, a, b);
    var sorted_health := SortSeq(processed_health);
    SortPreservesPositive(processed_health);
    result := CountKillableMonsters(sorted_health, a, k);
}
// </vc-code>

