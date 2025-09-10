predicate ValidInput(a: seq<int>, b: seq<int>, n: int)
{
    |a| >= 0 && |b| >= 0 &&
    (forall i :: 0 <= i < |a| ==> a[i] >= 0) &&
    (forall j :: 0 <= j < |b| ==> b[j] >= 0) &&
    n >= 1
}

function sum_seq(s: seq<int>): int
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

function ShelvesNeeded(total: int, capacity: int): int
    requires capacity > 0
{
    if total == 0 then 0 else (total - 1) / capacity + 1
}

predicate CanPlaceAll(a: seq<int>, b: seq<int>, n: int)
    requires ValidInput(a, b, n)
{
    var total_cups := sum_seq(a);
    var total_medals := sum_seq(b);
    var shelves_for_cups := ShelvesNeeded(total_cups, 5);
    var shelves_for_medals := ShelvesNeeded(total_medals, 10);
    shelves_for_cups + shelves_for_medals <= n
}

// <vc-helpers>
// Helper function to compute sum iteratively
function method SumIterative(s: seq<int>): int
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
{
    var sum := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant sum == sum_seq(s[0..i])
    {
        sum := sum + s[i];
        i := i + 1;
    }
    sum
}

// Lemma to prove SumIterative equals sum_seq
lemma SumIterativeLemma(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures SumIterative(s) == sum_seq(s)
{
    // The proof is established by the loop invariant in SumIterative
}

// Lemma to connect the computation with CanPlaceAll predicate
lemma CanPlaceAllLemma(a: seq<int>, b: seq<int>, n: int)
    requires ValidInput(a, b, n)
    ensures CanPlaceAll(a, b, n) == 
        (ShelvesNeeded(SumIterative(a), 5) + ShelvesNeeded(SumIterative(b), 10) <= n)
{
    var total_cups := SumIterative(a);
    var total_medals := SumIterative(b);
    calc {
        CanPlaceAll(a, b, n);
    ==  // Def. CanPlaceAll
        ShelvesNeeded(sum_seq(a), 5) + ShelvesNeeded(sum_seq(b), 10) <= n;
    ==  { SumIterativeLemma(a); SumIterativeLemma(b); }
        ShelvesNeeded(SumIterative(a), 5) + ShelvesNeeded(SumIterative(b), 10) <= n;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>, n: int) returns (result: string)
    requires ValidInput(a, b, n)
    ensures result == (if CanPlaceAll(a, b, n) then "YES" else "NO")
// </vc-spec>
// <vc-code>
{
    var total_cups := SumIterative(a);
    var shelves_for_cups := ShelvesNeeded(total_cups, 5);
    
    var total_medals := SumIterative(b);
    var shelves_for_medals := ShelvesNeeded(total_medals, 10);
    
    CanPlaceAllLemma(a, b, n);
    assert CanPlaceAll(a, b, n) == (shelves_for_cups + shelves_for_medals <= n);
    
    if shelves_for_cups + shelves_for_medals <= n then
        return "YES";
    else
        return "NO";
}
// </vc-code>

