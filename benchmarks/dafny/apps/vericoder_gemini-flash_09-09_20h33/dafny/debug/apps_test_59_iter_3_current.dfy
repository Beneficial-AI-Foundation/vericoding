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
function max_up_to_inductive(a: seq<int>, i: int): (m: int)
    requires 0 <= i < |a|
    ensures forall k :: 0 <= k <= i ==> a[k] <= m
    ensures exists k :: 0 <= k <= i && a[k] == m
    decreases i
{
    if i == 0 then a[0]
    else max(a[i], max_up_to_inductive(a, i-1))
}

lemma max_up_to_eq_max_up_to_inductive(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures max_up_to(a, i) == max_up_to_inductive(a, i)
    decreases i
{
    if i == 0 {
        // Base case: max_up_to(a, 0) == a[0] and max_up_to_inductive(a, 0) == a[0]
    } else {
        max_up_to_eq_max_up_to_inductive(a, i-1);
        // max_up_to(a, i) == if a[i] > max_up_to(a, i-1) then a[i] else max_up_to(a, i-1)
        //                   == if a[i] > max_up_to_inductive(a, i-1) then a[i] else max_up_to_inductive(a, i-1)  (by induction hypothesis)
        //                   == max(a[i], max_up_to_inductive(a, i-1))
        //                   == max_up_to_inductive(a, i)
    }
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
    var can_sort_result := true;
    for i := 0 to n - 2
        invariant 0 <= i <= n - 1
        invariant can_sort_result == (forall k :: 0 <= k < i ==> (p[k] == '0' ==> max_up_to(a, k) <= k + 1))
    {
        max_up_to_eq_max_up_to_inductive(a, i); // Prove equivalence for current i
        if p[i] == '0' {
            if max_up_to(a, i) > i + 1 {
                can_sort_result := false;
                break;
            }
        }
    }

    if can_sort_result {
        return "YES";
    } else {
        return "NO";
    }
}
// </vc-code>

