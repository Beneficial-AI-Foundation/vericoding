// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
