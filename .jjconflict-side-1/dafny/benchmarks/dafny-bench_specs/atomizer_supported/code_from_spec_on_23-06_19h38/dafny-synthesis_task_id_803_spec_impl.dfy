//IMPL 
method IsPerfectSquare(n: int) returns (result: bool)
    requires n >= 0
    ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
    ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
{
    if n == 0 {
        result := true;
        return;
    }
    
    var i := 0;
    while i * i < n
        invariant 0 <= i
        invariant forall j: int :: 0 <= j < i ==> j * j < n
    {
        i := i + 1;
    }
    
    if i * i == n {
        result := true;
    } else {
        result := false;
    }
}