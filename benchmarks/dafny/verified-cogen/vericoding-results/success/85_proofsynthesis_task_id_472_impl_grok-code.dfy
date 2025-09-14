// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsConsecutive(arr: array<int>)
  reads arr
  { arr.Length > 0 && forall i :: 0 <= i < arr.Length - 1 ==> arr[i] + 1 == arr[i+1] }

/* helper modified by LLM (iteration 2): fixed predicate body to avoid index out of bounds error in quantifier by adding bound check */
predicate ConsecutiveUpTo(arr: array<int>, n: int)
  reads arr
{ forall i :: 0 <= i < n && i+1 < arr.Length ==> arr[i] + 1 == arr[i+1] }
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(arr: array<int>) returns (is_consecutive: bool)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> (0 <= arr[i] + 1 < 2147483647)
    ensures is_consecutive == (forall i, j :: 0 <= i < j < arr.Length && j == i + 1 ==> (arr[i] + 1 == arr[j]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented logic with loop and invariant to verify consecutive numbers */
  var con := true;
  for i := 0 to arr.Length - 1
    invariant 0 <= i <= arr.Length
    invariant con <==> ConsecutiveUpTo(arr, i)
  {
    if i < arr.Length - 1 && arr[i] + 1 != arr[i+1] {
      con := false;
      break;
    }
  }
  is_consecutive := con && (arr.Length > 0);
}
// </vc-code>
