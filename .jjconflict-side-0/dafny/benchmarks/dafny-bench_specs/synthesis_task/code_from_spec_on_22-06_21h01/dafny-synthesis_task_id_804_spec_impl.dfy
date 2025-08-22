// ATOM
predicate IsEven(n: int)
{
    n % 2 == 0
}

// IMPL IsProductEven
method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
{
    result := false;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result <==> exists j :: 0 <= j < i && IsEven(a[j])
    {
        if IsEven(a[i]) {
            result := true;
            return;
        }
        i := i + 1;
    }
}