

// <vc-helpers>
lemma ForallGt(n: int, a: array<int>)
  requires forall k :: 0 <= k < a.Length ==> n > a[k]
  ensures forall i :: 0 <= i < a.Length ==> n > a[i]
{}
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
// </vc-spec>
// <vc-code>
{
    if a.Length == 0 {
        return true;
    }

    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> n > a[k]
    {
        if n <= a[i] {
            return false;
        }
        i := i + 1;
    }
    ForallGt(n, a); // Call the lemma to establish the postcondition
    return true;
}
// </vc-code>

