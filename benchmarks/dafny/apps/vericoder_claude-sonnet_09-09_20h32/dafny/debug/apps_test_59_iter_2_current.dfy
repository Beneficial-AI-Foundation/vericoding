predicate ValidInput(n: int, a: seq<int>, p: string)
{
    n >= 2 &&
    |a| == n &&
    |p| == n - 1 &&
    (forall i :: 0 <= i < |p| ==> p[i] == '0' || p[i] == '1') &&
    (forall i :: 0 <= i < |a| ==> 1 <= a[i] <= n) &&
    (forall i :: 1 <= i <= n ==> exists j :: 0 <= j < |a| && a[j] == i)
}

function max_up_to(a: seq<int>, i: int): int
    requires 0 <= i < |a|
    decreases i
{
    if i == 0 then a[0]
    else if a[i] > max_up_to(a, i-1) then a[i]
    else max_up_to(a, i-1)
}

predicate CanSort(n: int, a: seq<int>, p: string)
    requires ValidInput(n, a, p)
{
    forall i :: 0 <= i < n - 1 ==> 
        (p[i] == '0' ==> max_up_to(a, i) <= i + 1)
}

// <vc-helpers>
lemma MaxUpToMonotonic(a: seq<int>, i: int, j: int)
    requires 0 <= i <= j < |a|
    ensures max_up_to(a, i) <= max_up_to(a, j)
    decreases j - i
{
    if i == j {
        // Base case: trivially true
    } else {
        MaxUpToMonotonic(a, i, j-1);
        // max_up_to(a, j) is either a[j] or max_up_to(a, j-1)
        // In either case, max_up_to(a, i) <= max_up_to(a, j-1) <= max_up_to(a, j)
    }
}

lemma MaxUpToCorrect(a: seq<int>, i: int, k: int)
    requires 0 <= i < |a|
    requires 0 <= k <= i
    ensures a[k] <= max_up_to(a, i)
    decreases i - k
{
    if k == i {
        // a[i] <= max_up_to(a, i) by definition
    } else {
        if i == 0 {
            // k must be 0, so this is the base case
        } else {
            MaxUpToCorrect(a, i-1, k);
            // a[k] <= max_up_to(a, i-1) <= max_up_to(a, i)
        }
    }
}

lemma CanSortEquivalence(n: int, a: seq<int>, p: string)
    requires ValidInput(n, a, p)
    ensures CanSort(n, a, p) <==> (forall i :: 0 <= i < n - 1 ==> (p[i] == '0' ==> max_up_to(a, i) <= i + 1))
{
    // This is true by definition of CanSort
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, p: string) returns (result: string)
    requires ValidInput(n, a, p)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanSort(n, a, p)
// </vc-spec>
// <vc-code>
{
    for i := 0 to n - 2
        invariant 0 <= i <= n - 1
        invariant forall j :: 0 <= j < i ==> (p[j] == '0' ==> max_up_to(a, j) <= j + 1)
    {
        if p[i] == '0' {
            var max_val := max_up_to(a, i);
            if max_val > i + 1 {
                assert p[i] == '0' && max_up_to(a, i) > i + 1;
                assert !CanSort(n, a, p);
                return "NO";
            }
        }
    }
    assert forall j :: 0 <= j < n - 1 ==> (p[j] == '0' ==> max_up_to(a, j) <= j + 1);
    CanSortEquivalence(n, a, p);
    assert CanSort(n, a, p);
    return "YES";
}
// </vc-code>

