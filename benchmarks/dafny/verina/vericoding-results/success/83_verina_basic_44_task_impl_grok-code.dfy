// <vc-preamble>
predicate IsOdd(n: int)
{
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): helper function to check if all odd-indexed elements in the array are odd */
method ComputeIsOddAtIndexOdd(a: array<int>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < a.Length && i % 2 == 1 ==> IsOdd(a[i]))
{
  var isAllGood : bool := true;
  var i : int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant isAllGood ==> forall k :: 0 <= k < i ==> (k % 2 != 1 || IsOdd(a[k]))
    invariant !isAllGood ==> exists k :: 0 <= k < i && (k % 2 == 1 && !IsOdd(a[k]))
  {
    if i % 2 == 1 && !IsOdd(a[i]) {
      isAllGood := false;
    }
    i := i + 1;
  }
  result := isAllGood;
}
// </vc-helpers>

// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> (forall i :: 0 <= i < a.Length && i % 2 == 1 ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): call the helper function to check the condition */
  result := ComputeIsOddAtIndexOdd(a);
}
// </vc-code>
