function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}
// pure-end
method move_one_ball(a: seq<int>) returns (can: bool)
  // pre-conditions-start
  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]
  // pre-conditions-end
  // post-conditions-start
  ensures can <==> exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
  // post-conditions-end
{
  // impl-start
  if |a| <= 1 {
    assert is_sorted(a[..0]); // assert-line
    return true;
  }
  can := false;
  var i := 0;
  var min_index := 0;
  while i < |a|
    // invariants-start
    invariant 0 <= i <= |a|
    invariant 0 <= min_index < |a|
    invariant forall j :: 0 <= j < i && min_index != j ==> a[min_index] < a[j]
    // invariants-end
  {
    if a[i] < a[min_index] {
      min_index := i;
    }
    i := i + 1;
  }

  // assert-start
  assert forall j :: (
    0 <= j < |a| && min_index != j
    ==> (
      (forall i :: j <= i < |a| ==> a[j..][i - j] == a[i])
      && (forall i :: 0 <= i < j ==> (a[j..] + a[..j])[|a| - j + i] == a[i])
      && (
        if min_index < j then
          (a[j..] + a[..j])[|a| - j + min_index] == a[min_index]
        else
          (a[j..] + a[..j])[min_index - j] == a[min_index]
      )
      && (
        (exists p :: (
          1 <= p < |a[j..] + a[..j]|
          && (a[j..] + a[..j])[p] == a[min_index]
          && (a[j..] + a[..j])[0] > (a[j..] + a[..j])[p]
        )) ==> !is_sorted(a[j..] + a[..j])
      )
    )
  );
  // assert-end

  assert forall j :: 0 <= j < |a| && min_index != j ==> !is_sorted(a[j..] + a[..j]); // assert-line

  var new_a := a[min_index..] + a[..min_index];
  can := is_sorted(new_a);
  // impl-end
}
