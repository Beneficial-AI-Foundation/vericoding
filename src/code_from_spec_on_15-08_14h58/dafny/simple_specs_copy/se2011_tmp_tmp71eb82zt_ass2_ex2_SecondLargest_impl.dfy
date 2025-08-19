// IMPL ex2

method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
//ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
{
    var largest := a[0];
    var secondLargest := a[0];
    
    // Find the largest element
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] <= largest
        invariant largest in a[0..i]
    {
        if a[i] > largest {
            largest := a[i];
        }
        i := i + 1;
    }
    
    // Find the second largest element
    i := 0;
    var foundSecond := false;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant !foundSecond ==> secondLargest == a[0]
        invariant foundSecond ==> secondLargest in a[0..i]
        invariant foundSecond ==> secondLargest < largest
        /* code modified by LLM (iteration 3): Fixed invariant to properly handle the case where secondLargest is the maximum among elements less than largest */
        invariant foundSecond ==> forall k :: 0 <= k < i && a[k] < largest ==> a[k] <= secondLargest
        invariant foundSecond ==> exists k :: 0 <= k < i && a[k] == secondLargest && a[k] < largest
    {
        /* code modified by LLM (iteration 3): Fixed logic to ensure invariant is maintained */
        if a[i] < largest {
            if !foundSecond {
                secondLargest := a[i];
                foundSecond := true;
            } else if a[i] > secondLargest {
                secondLargest := a[i];
            }
        }
        i := i + 1;
    }
    
    seclar := secondLargest;
}