//IMPL 
method IsPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (forall k :: 2 <= k < n ==> n % k != 0)
{
    var i := 2;
    result := true;
    
    while i < n
        invariant 2 <= i <= n
        invariant result <==> (forall k :: 2 <= k < i ==> n % k != 0)
    {
        if n % i == 0 {
            result := false;
            return;
        }
        i := i + 1;
    }
}