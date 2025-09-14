// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSorted(lst: array<int>) returns (result: bool)
    requires lst.Length >= 1
    ensures result ==> forall i, j :: 0 <= i && i < j && j < lst.Length ==> lst[i] <= lst[j]
    ensures !result ==> exists i, j :: 0 <= i && i < j && j < lst.Length && lst[i] > lst[j]
// </vc-spec>
// <vc-code>
{
var i := 0;
var isSorted := true;
while i < lst.Length - 1
  invariant 0 <= i <= lst.Length - 1
  invariant isSorted ==> forall k,j :: 0 <= k && k < j && j <= i ==> lst[k] <= lst[j]
  invariant !isSorted ==> exists k,j :: 0 <= k && k < j && j < lst.Length && (j <= i) && lst[k] > lst[j]
{
  if lst[i] > lst[i+1] {
    isSorted := false;
  }
  i := i + 1;
}
result := isSorted;
}
// </vc-code>
