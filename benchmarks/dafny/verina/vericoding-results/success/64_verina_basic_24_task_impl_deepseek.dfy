// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added decreases clauses for termination */
function FirstEvenIndex(a: array<int>, start: int): (index: int)
  requires 0 <= start < a.Length
  requires exists x :: start <= x < a.Length && IsEven(a[x])
  reads a
  ensures start <= index < a.Length && IsEven(a[index])
  ensures forall k :: start <= k < index ==> IsOdd(a[k])
  decreases a.Length - start
{
  if IsEven(a[start]) then start
  else FirstEvenIndex(a, start + 1)
}
function FirstOddIndex(a: array<int>, start: int): (index: int)
  requires 0 <= start < a.Length
  requires exists x :: start <= x < a.Length && IsOdd(a[x])
  reads a
  ensures start <= index < a.Length && IsOdd(a[index])
  ensures forall k :: start <= k < index ==> IsEven(a[k])
  decreases a.Length - start
{
  if IsOdd(a[start]) then start
  else FirstOddIndex(a, start + 1)
}
// </vc-helpers>

// <vc-spec>
method FirstEvenOddDifference(a: array<int>) returns (result: int)
    requires 
        a.Length > 1 &&
        (exists x :: 0 <= x < a.Length && IsEven(a[x])) &&
        (exists x :: 0 <= x < a.Length && IsOdd(a[x]))
    ensures 
        exists i, j :: 
            0 <= i < a.Length && 0 <= j < a.Length &&
            IsEven(a[i]) && IsOdd(a[j]) &&
            result == a[i] - a[j] &&
            (forall k :: 0 <= k < i ==> IsOdd(a[k])) &&
            (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed implementation to satisfy postconditions */
{
  var firstEvenIndex := FirstEvenIndex(a, 0);
  var firstOddIndex := FirstOddIndex(a, 0);
  result := a[firstEvenIndex] - a[firstOddIndex];
}
// </vc-code>
