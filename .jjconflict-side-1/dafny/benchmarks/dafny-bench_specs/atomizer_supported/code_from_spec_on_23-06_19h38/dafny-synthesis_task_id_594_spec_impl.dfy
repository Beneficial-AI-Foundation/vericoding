// ATOM 
predicate IsEven(n: int)
{
    n % 2 == 0
}


// ATOM 

predicate IsOdd(n: int)
{
    n % 2 != 0
}


// IMPL 

method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
{
    var firstEvenIndex := -1;
    var firstOddIndex := -1;
    
    // Find first even number
    var i := 0;
    while i < a.Length && firstEvenIndex == -1
        invariant 0 <= i <= a.Length
        invariant firstEvenIndex == -1 ==> forall k :: 0 <= k < i ==> IsOdd(a[k])
        invariant firstEvenIndex != -1 ==> 0 <= firstEvenIndex < i && IsEven(a[firstEvenIndex]) && forall k :: 0 <= k < firstEvenIndex ==> IsOdd(a[k])
    {
        if IsEven(a[i]) {
            firstEvenIndex := i;
        }
        i := i + 1;
    }
    
    // Find first odd number
    var j := 0;
    while j < a.Length && firstOddIndex == -1
        invariant 0 <= j <= a.Length
        invariant firstOddIndex == -1 ==> forall k :: 0 <= k < j ==> IsEven(a[k])
        invariant firstOddIndex != -1 ==> 0 <= firstOddIndex < j && IsOdd(a[firstOddIndex]) && forall k :: 0 <= k < firstOddIndex ==> IsEven(a[k])
    {
        if IsOdd(a[j]) {
            firstOddIndex := j;
        }
        j := j + 1;
    }
    
    diff := a[firstEvenIndex] - a[firstOddIndex];
}