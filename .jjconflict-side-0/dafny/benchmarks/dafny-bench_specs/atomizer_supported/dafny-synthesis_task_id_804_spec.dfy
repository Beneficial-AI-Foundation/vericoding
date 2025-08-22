// ATOM 
predicate IsEven(n: int)
{
    n % 2 == 0
}


// SPEC 

method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
{
}
