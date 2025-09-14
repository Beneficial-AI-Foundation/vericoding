predicate ValidInput(n: int, f: seq<int>)
{
    n >= 2 && n <= 5000 &&
    |f| == n &&
    forall i :: 0 <= i < |f| ==> 1 <= f[i] <= n && f[i] != i + 1
}

function ZeroIndexedArray(n: int, f: seq<int>): seq<int>
    requires ValidInput(n, f)
{
    seq(n, j requires 0 <= j < n => f[j] - 1)
}

predicate HasLoveTriangleWith(n: int, a: seq<int>)
    requires |a| == n
    requires forall k :: 0 <= k < n ==> 0 <= a[k] < n
{
    exists i {:trigger a[i], a[a[i]], a[a[a[i]]]} :: 0 <= i < n && 
        0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i
}

predicate HasLoveTriangle(n: int, f: seq<int>)
    requires ValidInput(n, f)
{
    var a := ZeroIndexedArray(n, f);
    HasLoveTriangleWith(n, a)
}

// <vc-helpers>
lemma AboutHasLoveTriangleWith(n: int, a: seq<int>)
    requires |a| == n
    requires forall k :: 0 <= k < n ==> 0 <= a[k] < n
    ensures HasLoveTriangleWith(n, a) <==> exists i :: 0 <= i < n && a[a[a[i]]] == i
{
    calc {
        HasLoveTriangleWith(n, a);
    ==  // def. HasLoveTriangleWith
        exists i :: 0 <= i < n && a[a[a[i]]] == i;
    }
    
    if exists i :: 0 <= i < n && a[a[a[i]]] == i {
        var i0 :| 0 <= i0 < n && a[a[a[i0]]] == i0;
        assert a[i0] < n;
        assert a[a[i0]] < n;
        assert a[a[a[i0]]] == i0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, f: seq<int>) returns (result: string)
    requires ValidInput(n, f)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> HasLoveTriangle(n, f)
// </vc-spec>
// <vc-code>
{
    var a := ZeroIndexedArray(n, f);
    
    for i := 0 to n
        invariant 0 <= i <= n
        invariant forall j {:trigger a[j]} :: 0 <= j < i ==> 0 <= a[j] < n
    {
        if i < n {
            assert 0 <= i < n;
            assert a[i] == f[i] - 1;
            assert 1 <= f[i] <= n;
            calc {
                a[i];
            ==  // def. a
                f[i] - 1;
            >=  // by premise
                1 - 1;
            ==  // arithmetic
                0;
            }
            calc {
                a[i];
            ==  // def. a
                f[i] - 1;
            <=  // by premise
                n - 1;
            <   // arithmetic
                n;
            }
            assert 0 <= a[i] < n;
        }
    }
    
    assert forall k :: 0 <= k < n ==> 0 <= a[k] < n;
    
    calc {
        HasLoveTriangle(n, f);
    ==  // def. HasLoveTriangle
        var a' := ZeroIndexedArray(n, f);
        HasLoveTriangleWith(n, a');
    ==  // a' == a
        HasLoveTriangleWith(n, a);
    }
    
    AboutHasLoveTriangleWith(n, a);
    
    if exists i :: 0 <= i < n && a[a[a[i]]] == i {
        result := "YES";
    } else {
        result := "NO";
    }

    if result == "YES" {
        assert exists i :: 0 <= i < n && a[a[a[i]]] == i;
        calc {
            HasLoveTriangle(n, f);
        ==  // proved above
            HasLoveTriangleWith(n, a);
        ==  // lemma application
            exists i :: 0 <= i < n && a[a[a[i]]] == i;
        }
        assert HasLoveTriangle(n, f);
    } else {
        assert result == "NO";
        assert !(exists i :: 0 <= i < n && a[a[a[i]]] == i);
        calc {
            !(exists i :: 0 <= i < n && a[a[a[i]]] == i);
        ==  // lemma application
            !HasLoveTriangleWith(n, a);
        ==  // proved above
            !HasLoveTriangle(n, f);
        }
        assert !HasLoveTriangle(n, f);
    }
}
// </vc-code>

