predicate IsOdd(n: int)
{
    n % 2 == 1
}

// <vc-helpers>
lemma OddIndexImpliesOddValue(a: array<int>)
  ensures forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i])) <==> 
          forall i :: 0 <= i < a.Length && IsOdd(i) ==> IsOdd(a[i])
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]))
// </vc-spec>
// </vc-spec>

// <vc-code>
method IsOddAtIndexOddImpl(a: array<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]))
{
    result := true;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result <==> forall k :: 0 <= k < i ==> (IsOdd(k) ==> IsOdd(a[k]))
    {
        if IsOdd(i) && !IsOdd(a[i])
        {
            result := false;
            break;
        }
        i := i + 1;
    }
    if result {
        assert forall k :: 0 <= k < a.Length ==> (IsOdd(k) ==> IsOdd(a[k]));
    }
}
// </vc-code>
