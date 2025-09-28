// <vc-preamble>
predicate IsOdd(x: int)
{
    x % 2 != 0
}

datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
predicate AllEvenUpTo(a: array<int>, idx: nat)
  requires idx <= a.Length
  reads a
{
  forall j | 0 <= j < idx :: !IsOdd(a[j])
}

lemma FirstOddLemma(a: array<int>, idx: nat)
  requires idx <= a.Length
  requires AllEvenUpTo(a, idx)
  requires forall i | 0 <= i < a.Length :: !IsOdd(a[i])
  ensures forall j | 0 <= j < idx :: !IsOdd(a[j])
{
}
// </vc-helpers>

// <vc-spec>
method FindFirstOdd(a: array<int>) returns (result: Option<nat>)
    requires a.Length > 0
    ensures
        match result {
            case Some(idx) => idx < a.Length && IsOdd(a[idx]) &&
                forall j :: 0 <= j < idx ==> !IsOdd(a[j])
            case None => forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
        }
// </vc-spec>
// <vc-code>
{
    var i: nat := 0;
    while i < a.Length
        invariant i <= a.Length
        invariant AllEvenUpTo(a, i)
    {
        if IsOdd(a[i]) {
            return Some(i);
        }
        i := i + 1;
    }
    return None;
}
// </vc-code>
