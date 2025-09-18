// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatch by changing arr[1..] to arr[1..arr.Length] which results into array<int> instead of seq<int>*/
predicate is_sorted(arr: array<int>)
  reads arr
  requires arr.Length >= 0
{
  if arr.Length <= 1 then true
  else arr[0] <= arr[1] && is_sorted(arr[1..arr.Length])
}
// </vc-helpers>

// <vc-spec>
method insertion_sort(l: array<int>) returns (result: array<int>)
    ensures
        /* The result is sorted in non-decreasing order */
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        /* The result is a permutation of the input */
        result.Length == l.Length && multiset(result[..]) == multiset(l[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type errors related to `is_sorted` predicate. Also fixed issues with array slicing to ensure correct type for helper function calls.*/
{
    if l == null {
        result := new int[0];
        return result;
    }

    result := new int[l.Length];

    if l.Length == 0 {
        return result;
    }

    var a := new int[l.Length];
    // Manually copy the elements since Array.Copy is not available in Dafny
    var k := 0;
    while k < l.Length
        invariant 0 <= k <= l.Length
        invariant forall x :: 0 <= x < k ==> a[x] == l[x]
    {
        a[k] := l[k];
        k := k + 1;
    }

    var i := 1;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant is_sorted(a[..i])
        invariant multiset(a[..]) == multiset(l[..])

    {
        var key := a[i];
        var j := i - 1;
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant forall x :: j + 1 <= x < i ==> a[x] == old(a[x])
            invariant forall x :: 0 <= x <= j ==> a[x] == old(a[x])
            invariant is_sorted(a[..j+1])
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        a[j + 1] := key;
        i := i + 1;
    }

    result := a;
}
// </vc-code>
