// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method can_arrange(arr: seq<int>) returns (pos: int)

  requires |arr| > 0
  requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]

  ensures pos == -1 ==> forall i :: 1 <= i < |arr| ==> arr[i] >= arr[i - 1]
  ensures pos >= 0 ==> 1 <= pos < |arr| && arr[pos] < arr[pos - 1]
  ensures pos >= 0 ==> forall i :: pos < i < |arr| ==> arr[i] >= arr[i - 1]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added invariant to track last violation and ensure postconditions */ {
  pos := -1;
  var i := 1;
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant if pos >= 0 then 
                (1 <= pos < i && arr[pos] < arr[pos-1] && 
                 forall j :: pos < j < i ==> arr[j] >= arr[j-1])
              else 
                forall j :: 1 <= j < i ==> arr[j] >= arr[j-1]
  {
    if arr[i] < arr[i - 1] {
      pos := i;
    }
    i := i + 1;
  }
}
// </vc-code>
