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
lemma ShelvesNeededLowerBound(total: int, capacity: int)
    requires capacity > 0
    requires total >= 0
    ensures ShelvesNeeded(total, capacity) >= 0
{
    if total == 0 {
    } else {
    }
}

lemma ShelvesNeededMonotonic(total1: int, total2: int, capacity: int)
    requires capacity > 0
    requires 0 <= total1 <= total2
    ensures ShelvesNeeded(total1, capacity) <= ShelvesNeeded(total2, capacity)
{
    if total1 == 0 || total2 == 0 {
    } else {
        calc {
            (total1 - 1) / capacity + 1;
            <= (total2 - 1) / capacity + 1;
            { assert total1 <= total2; }
        }
    }
}

lemma ShelvesNeededFormula(total: int, capacity: int)
    requires capacity > 0
    requires total >= 0
    ensures ShelvesNeeded(total, capacity) == (if total == 0 then 0 else (total - 1) / capacity + 1)
{
}

lemma sum_seq_nonnegative(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures sum_seq(s) >= 0
{
    if |s| == 0 {
    } else {
        sum_seq_nonnegative(s[1..]);
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
    var total_cups := sum_seq(a);
    var total_medals := sum_seq(b);
    
    sum_seq_nonnegative(a);
    sum_seq_nonnegative(b);
    
    var shelves_for_cups := ShelvesNeeded(total_cups, 5);
    var shelves_for_medals := ShelvesNeeded(total_medals, 10);
    
    ShelvesNeededLowerBound(total_cups, 5);
    ShelvesNeededLowerBound(total_medals, 10);
    
    if shelves_for_cups + shelves_for_medals <= n {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

