// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PalVerify(a: array<char>) returns (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j])
// </vc-spec>
// <vc-code>
{
  yn := true;
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall k :: 0 <= k < i ==> a[k] == a[a.Length - 1 - k]
    decreases a.Length / 2 - i
  {
    if a[i] != a[a.Length - 1 - i] {
      yn := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
