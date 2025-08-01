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
    var max := a[0];
    var secondMax := a[0];
    
    for i := 1 to a.Length {
        if a[i] > max {
            secondMax := max;
            max := a[i];
        } else if a[i] > secondMax && a[i] < max {
            secondMax := a[i];
        }
    }
    
    seclar := secondMax;
}

//IMPL Main
method Main()
{
}