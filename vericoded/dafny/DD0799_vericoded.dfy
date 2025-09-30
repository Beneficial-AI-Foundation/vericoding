predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
// </vc-spec>
// <vc-code>
{
    result := true;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant result <==> forall j :: 0 <= j < i ==> (IsEven(j) ==> IsEven(lst[j]))
    {
        if IsEven(i) && !IsEven(lst[i]) {
            result := false;
        }
        i := i + 1;
    }
}
// </vc-code>

