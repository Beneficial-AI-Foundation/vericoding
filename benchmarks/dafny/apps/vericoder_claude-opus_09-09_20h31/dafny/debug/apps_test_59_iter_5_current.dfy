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
lemma MaxUpToProperties(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures a[i] <= max_up_to(a, i)
    ensures forall j :: 0 <= j <= i ==> a[j] <= max_up_to(a, i)
    decreases i
{
    if i == 0 {
        assert a[0] <= max_up_to(a, 0);
    } else {
        MaxUpToProperties(a, i-1);
        if a[i] > max_up_to(a, i-1) {
            assert max_up_to(a, i) == a[i];
            assert forall j :: 0 <= j <= i-1 ==> a[j] <= max_up_to(a, i-1) <= a[i] == max_up_to(a, i);
        } else {
            assert max_up_to(a, i) == max_up_to(a, i-1);
            assert forall j :: 0 <= j <= i-1 ==> a[j] <= max_up_to(a, i);
        }
    }
}

lemma MaxUpToMonotonic(a: seq<int>, i: int, j: int)
    requires 0 <= i <= j < |a|
    ensures max_up_to(a, i) <= max_up_to(a, j)
    decreases j - i
{
    if i == j {
        assert max_up_to(a, i) == max_up_to(a, j);
    } else if i == j - 1 {
        if a[j] > max_up_to(a, j-1) {
            assert max_up_to(a, j) == a[j] >= max_up_to(a, j-1) == max_up_to(a, i);
        } else {
            assert max_up_to(a, j) == max_up_to(a, j-1) == max_up_to(a, i);
        }
    } else {
        MaxUpToMonotonic(a, i, j-1);
        if a[j] > max_up_to(a, j-1) {
            assert max_up_to(a, j) == a[j] >= max_up_to(a, j-1) >= max_up_to(a, i);
        } else {
            assert max_up_to(a, j) == max_up_to(a, j-1) >= max_up_to(a, i);
        }
    }
}

predicate ValidInputFixed(n: int, a: seq<int>, p: string)
{
    n >= 2 &&
    |a| == n &&
    |p| == n - 1 &&
    (forall i :: 0 <= i < |p| ==> p[i] == '0' || p[i] == '1') &&
    (forall i :: 0 <= i < |a| ==> 1 <= a[i] <= n) &&
    (forall i {:trigger a[i]} :: 1 <= i <= n ==> exists j :: 0 <= j < |a| && a[j] == i)
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
    var canSort := true;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant canSort <==> (forall j :: 0 <= j < i ==> (p[j] == '0' ==> max_up_to(a, j) <= j + 1))
    {
        if p[i] == '0' {
            var maxVal := a[0];
            var j := 1;
            
            while j <= i
                invariant 1 <= j <= i + 1
                invariant maxVal == max_up_to(a, j-1)
            {
                if a[j] > maxVal {
                    maxVal := a[j];
                }
                j := j + 1;
            }
            
            assert maxVal == max_up_to(a, i);
            
            if maxVal > i + 1 {
                canSort := false;
            }
        }
        i := i + 1;
    }
    
    if canSort {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

