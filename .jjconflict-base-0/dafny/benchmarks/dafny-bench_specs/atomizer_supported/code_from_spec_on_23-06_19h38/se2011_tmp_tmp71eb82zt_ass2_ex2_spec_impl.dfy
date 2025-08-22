// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

//IMPL SecondLargest
method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
//ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
{
    if a.Length == 1 {
        seclar := a[0];
        return;
    }
    
    var largest := a[0];
    var secondLargest := a[0];
    
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant largest >= secondLargest
        invariant forall k :: 0 <= k < i ==> a[k] <= largest
        invariant forall k :: 0 <= k < i ==> (a[k] <= secondLargest || a[k] == largest)
    {
        if a[i] > largest {
            secondLargest := largest;
            largest := a[i];
        } else if a[i] > secondLargest {
            secondLargest := a[i];
        }
        i := i + 1;
    }
    
    seclar := secondLargest;
}

//IMPL Main
method Main()
{
}