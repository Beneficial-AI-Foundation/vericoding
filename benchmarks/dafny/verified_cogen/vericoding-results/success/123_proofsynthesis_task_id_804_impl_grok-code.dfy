// <vc-preamble>
predicate IsEven(n: int)
{
    (n % 2) == 0
}
// </vc-preamble>

// <vc-helpers>

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
    decreases arr.Length - i
    invariant 0 <= i <= arr.Length
    invariant found <==> exists j :: 0 <= j < i && IsEven(arr[j])
  {
    if IsEven(arr[i]) {
      found := true;
      break;
    }
    i := i + 1;
  }
  result := found;
}
// </vc-code>
