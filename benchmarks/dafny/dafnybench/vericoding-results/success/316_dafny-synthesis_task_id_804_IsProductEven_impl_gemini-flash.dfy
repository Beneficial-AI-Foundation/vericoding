predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
lemma lemma_product_even_iff_any_even(a: array<int>)
  ensures (exists i :: 0 <= i < a.Length && IsEven(a[i])) <==> (forall i :: 0 <= i < a.Length ==> !IsEven(a[i])) != true
{}
// </vc-helpers>

// <vc-spec>
method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
// </vc-spec>
// <vc-code>
{
  var foundEven: bool := false;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant foundEven <==> (exists k :: 0 <= k < i && IsEven(a[k]))
  {
    if IsEven(a[i])
    {
      foundEven := true;
    }
  }
  return foundEven;
}
// </vc-code>

