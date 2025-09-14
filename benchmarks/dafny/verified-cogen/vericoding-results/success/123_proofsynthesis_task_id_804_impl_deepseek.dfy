// <vc-preamble>
predicate IsEven(n: int)
{
    (n % 2) == 0
}
// </vc-preamble>

// <vc-helpers>
lemma HelperLemma(n: int)
  requires n >= 0
  ensures IsEven(n) <==> (n % 2 == 0)
{
}
// </vc-helpers>

// <vc-spec>
method IsProductEven(arr: array<int>) returns (result: bool)
    ensures result <==> (exists k :: 0 <= k < arr.Length && IsEven(arr[k]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := false;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant !result ==> !(exists k :: 0 <= k < i && IsEven(arr[k]))
    invariant result ==> (exists k :: 0 <= k < i && IsEven(arr[k]))
  {
    if IsEven(arr[i]) {
      result := true;
    }
    i := i + 1;
  }
}
// </vc-code>
