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
    var maxIndex := 0;
    var i := 1;
    
    // Find the maximum element and its index
    while i < a.Length
    {
        if a[i] > max {
            max := a[i];
            maxIndex := i;
        }
        i := i + 1;
    }
    
    // Find the second largest (largest among non-maximum elements)
    seclar := max;
    i := 0;
    while i < a.Length
    {
        if i != maxIndex && a[i] > seclar {
            seclar := a[i];
        } else if i != maxIndex && a[i] < max && a[i] > seclar {
            seclar := a[i];
        }
        i := i + 1;
    }
    
    // If no distinct second largest found, seclar remains as max
    if seclar == max {
        // Find the largest element that's smaller than max
        var found := false;
        i := 0;
        while i < a.Length
        {
            if a[i] < max && (!found || a[i] > seclar) {
                seclar := a[i];
                found := true;
            }
            i := i + 1;
        }
        // If no smaller element found, seclar remains as max
    }
}

//ATOM_PLACEHOLDER_Main