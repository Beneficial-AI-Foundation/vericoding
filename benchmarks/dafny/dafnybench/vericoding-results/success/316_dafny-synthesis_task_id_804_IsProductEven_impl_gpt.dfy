predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var found := false;
  var k := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant found ==> 0 <= k < i && IsEven(a[k])
    invariant !found ==> forall j :: 0 <= j < i ==> !IsEven(a[j])
  {
    if IsEven(a[i]) {
      found := true;
      k := i;
    }
    i := i + 1;
  }
  result := found;
  if result {
    assert 0 <= k < a.Length && IsEven(a[k]);
    assert exists j :: 0 <= j < a.Length && IsEven(a[j]);
  } else {
    assert forall j :: 0 <= j < a.Length ==> !IsEven(a[j]);
    assert !(exists j :: 0 <= j < a.Length && IsEven(a[j]));
  }
}
// </vc-code>

