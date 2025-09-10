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
predicate IsSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Insert(x: int, s: seq<int>): seq<int>
    requires IsSorted(s)
    requires forall i :: 0 <= i < |s| ==> s[i] > 0
    requires x > 0
    ensures IsSorted(Insert(x, s))
    ensures x in Insert(x, s)
    ensures multiset(Insert(x, s)) == multiset(s) + multiset{x}
    ensures forall i :: 0 <= i < |Insert(x, s)| ==> Insert(x, s)[i] > 0
    ensures |Insert(x, s)| == |s| + 1
{
    if |s| == 0 then [x]
    else if x <= s[0] then [x] + s
    else {
        var rest := Insert(x, s[1..]);
        assert s[0] <= rest[0];
        [s[0]] + rest
    }
}

function Sort(s: seq<int>): seq<int>
    requires forall i :: 0 <= i < |s| ==> s[i] > 0
    ensures IsSorted(Sort(s))
    ensures multiset(Sort(s)) == multiset(s)
    ensures forall i :: 0 <= i < |Sort(s)| ==> Sort(s)[i] > 0
    ensures |Sort(s)| == |s|
{
    if |s| == 0 then []
    else {
        var sorted_tail := Sort(s[1..]);
        assert |sorted_tail| == |s[1..]|;
        Insert(s[0], sorted_tail)
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
    var processed := ProcessHealthValues(H, a, b);
    var sorted := Sort(processed);
    result := CountKillableMonsters(sorted, a, k);
}
// </vc-code>

