predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> !IsEven(a[j])
  {
    if IsEven(a[i]) {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

