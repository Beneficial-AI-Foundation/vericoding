// <vc-preamble>
predicate IsEven(n: int)
{
    (n % 2) == 0
}
// </vc-preamble>

// <vc-helpers>
predicate ExistsEvenInPrefix(arr: array<int>, n: int)
  requires 0 <= n <= arr.Length
  reads arr
{
  exists k :: 0 <= k < n && IsEven(arr[k])
}

function ExistsEvenInArray(arr: array<int>): bool
  reads arr
{
  exists k :: 0 <= k < arr.Length && IsEven(arr[k])
}
// </vc-helpers>

// <vc-spec>
method IsProductEven(arr: array<int>) returns (result: bool)
    ensures result <==> (exists k :: 0 <= k < arr.Length && IsEven(arr[k]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var found := false;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant found ==> (exists k :: 0 <= k < i && IsEven(arr[k]))
    invariant !found ==> (forall k :: 0 <= k < i ==> !IsEven(arr[k]))
    decreases arr.Length - i
  {
    if IsEven(arr[i]) {
      found := true;
    }
    i := i + 1;
  }
  result := found;
}
// </vc-code>
