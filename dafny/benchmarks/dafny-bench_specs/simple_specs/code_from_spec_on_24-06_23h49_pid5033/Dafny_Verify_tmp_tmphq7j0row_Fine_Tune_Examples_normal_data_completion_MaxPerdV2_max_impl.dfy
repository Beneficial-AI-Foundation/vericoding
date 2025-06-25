//ATOM

function is_max(m: int, a: array<int>, n: int): bool
reads a
 requires n <= a.Length
{
 contains(m, a, n) && upper_bound(m, a, n)
}


//ATOM
function contains(v: int, a: array<int>, n: int): bool
reads a
 requires n <= a.Length
{
 exists j :: 0 <= j < n && a[j] == v
}


//ATOM

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
 requires n <= a.Length
{
 forall j :: 0 <= j < n ==> a[j] <= v
}


//IMPL max

method max(a: array<int>, n: int) returns (max: int)
 requires 0 < n <= a.Length
 ensures is_max(max, a, n)
{
    max := a[0];
    var i := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant contains(max, a, i)
        invariant upper_bound(max, a, i)
    {
        if a[i] > max {
            max := a[i];
        }
        i := i + 1;
    }
}