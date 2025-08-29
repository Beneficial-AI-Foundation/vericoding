function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
lemma is_sorted_concatenation(a: seq<int>, b: seq<int>)
  requires is_sorted(a)
  requires is_sorted(b)
  requires |a| > 0 && |b| > 0
  requires a[|a|-1] <= b[0]
  ensures is_sorted(a + b)
{
  var c := a + b;
  forall i, j | 0 <= i < j < |c|
    ensures c[i] <= c[j]
  {
    if j < |a| {
      assert c[i] == a[i] && c[j] == a[j];
    } else if i >= |a| {
      assert c[i] == b[i - |a|] && c[j] == b[j - |a|];
    } else {
      assert i < |a| <= j;
      assert c[i] == a[i] && c[j] == b[j - |a|];
      assert a[i] <= a[|a|-1] <= b[0] <= b[j - |a|];
    }
  }
}

lemma rotation_properties(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures |a[i..] + a[..i]| == |a|
  ensures forall k :: 0 <= k < |a[i..]| ==> (a[i..] + a[..i])[k] == a[i + k]
  ensures forall k :: 0 <= k < |a[..i]| ==> (a[i..] + a[..i])[|a[i..]| + k] == a[k]
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def move_one_ball(arr: List[int]) -> bool
We have an array 'arr' of N integers arr[1], arr[2], ..., arr[N].The numbers in the array will be randomly ordered. Your task is to determine if it is possible to get an array sorted in non-decreasing order by performing the following operation on the given array: You are allowed to perform right shift operation any number of times.
*/
// </vc-description>

// <vc-spec>
method move_one_ball(a: seq<int>) returns (can: bool)
  // pre-conditions-start
  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]
  // pre-conditions-end
  // post-conditions-start
  ensures can <==> exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  can := false;
  
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant can <==> exists j :: 0 <= j < i && is_sorted(a[j..] + a[..j])
  {
    var rotated := a[i..] + a[..i];
    
    if is_sorted(rotated) {
      can := true;
      return;
    }
  }
}
// </vc-code>

