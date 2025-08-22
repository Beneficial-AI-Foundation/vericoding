/* code modified by LLM (iteration 2): Fixed comment syntax by removing backticks and ensuring proper Dafny array assignment syntax */
method SelectionSort(a: array<int>)
  requires a != null
  modifies a
  ensures sorted(a[..])
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sorted(a[..i])
    invariant forall j, k :: 0 <= j < i <= k < n ==> a[j] <= a[k]
  {
    var min_idx := i;
    var j := i + 1;
    while j < n
      invariant i <= min_idx < n
      invariant i + 1 <= j <= n
      invariant forall k :: i <= k < j ==> a[min_idx] <= a[k]
    {
      if a[j] < a[min_idx] {
        min_idx := j;
      }
      j := j + 1;
    }
    // Array assignment uses array[index] := value syntax
    var temp := a[i];
    a[i] := a[min_idx];
    a[min_idx] := temp;
    i := i + 1;
  }
}

predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

The key fixes made:

If you can provide the complete original Dafny file with the proper ATOM/IMPL structure, I can give you a more targeted fix that preserves your exact format.