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
    ensures max_up_to(a, i) >= a[i]
    ensures forall j :: 0 <= j <= i ==> max_up_to(a, i) >= a[j]
    decreases i
{
    if i > 0 {
        MaxUpToProperties(a, i-1);
    }
}

lemma MaxUpToMonotonic(a: seq<int>, i: int, j: int)
    requires 0 <= i <= j < |a|
    ensures max_up_to(a, i) <= max_up_to(a, j)
    decreases j - i
{
    if i < j {
        MaxUpToProperties(a, j);
        assert max_up_to(a, j) >= a[j] && max_up_to(a, j) >= max_up_to(a, j-1);
        MaxUpToMonotonic(a, i, j-1);
    }
}

lemma MaxUpToMax(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures forall k :: 0 <= k <= i ==> max_up_to(a, i) >= a[k]
    decreases i
{
    if i > 0 {
        MaxUpToMax(a, i-1);
    }
}

lemma MaxUpToDefinition(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures (i == 0 ==> max_up_to(a, i) == a[0]) &&
            (i > 0 ==> (a[i] > max_up_to(a, i-1) ==> max_up_to(a, i) == a[i]) && 
                      (a[i] <= max_up_to(a, i-1) ==> max_up_to(a, i) == max_up_to(a, i-1)))
    decreases i
{
    if i > 0 {
        MaxUpToDefinition(a, i-1);
    }
}

lemma MaxUpToEquality(a: seq<int>, i: int, m: int)
    requires 0 <= i < |a|
    requires m == (if i == 0 then a[0] else if a[i] > max_up_to(a, i-1) then a[i] else max_up_to(a, i-1))
    ensures m == max_up_to(a, i)
    decreases i
{
    if i > 0 {
        MaxUpToDefinition(a, i-1);
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
    var max_so_far := a[0];
    var valid := true;
    var i := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant max_so_far == max_up_to(a, i-1)
        invariant valid == (forall k :: 0 <= k < i-1 ==> (p[k] == '0' ==> max_up_to(a, k) <= k + 1))
    {
        if p[i-1] == '0' && max_so_far > i {
            valid := false;
        }
        
        if a[i] > max_so_far {
            max_so_far := a[i];
        } else {
            max_so_far := max_so_far;
        }
        
        assert max_so_far == max_up_to(a, i) by {
            MaxUpToDefinition(a, i);
            if i > 0 {
                if a[i] > max_up_to(a, i-1) {
                    assert max_up_to(a, i) == a[i];
                } else {
                    assert max_up_to(a, i) == max_up_to(a, i-1);
                }
            }
        }
        
        i := i + 1;
    }
    
    if valid {
        assert CanSort(n, a, p);
        return "YES";
    } else {
        assert !CanSort(n, a, p);
        return "NO";
    }
}
// </vc-code>

