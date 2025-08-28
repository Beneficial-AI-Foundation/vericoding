type BiggestMap = map<int, int>

method count(a: seq<int>) returns (biggest: BiggestMap)
  // post-conditions-start
  ensures forall i :: 0 <= i < |a| && a[i] in biggest ==>
    biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==>
    biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==>
    biggest[a[i]] == biggest[a[j]]
  // post-conditions-end
{
  // impl-start
  if |a| == 0 {
    return map[];
  }
  var cnt := map[];
  ghost var positions := map[];
  var i := 0;
  while i < |a|
    // invariants-start
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> a[j] in positions && positions[a[j]] == set k | 0 <= k < i && a[k] == a[j]
    invariant forall j :: 0 <= j < i ==> a[j] in cnt && cnt[a[j]] == |positions[a[j]]|
    invariant forall j :: j in positions ==> forall k :: k in positions[j] ==> k < i

    invariant forall x :: x in positions ==> x in a[..i]
    invariant forall x :: x in positions ==> x in cnt && cnt[x] == |positions[x]|
    invariant forall x :: x in cnt ==> x in positions
    // invariants-end
  {
    if a[i] in cnt {
      ghost var pre := positions[a[i]];
      positions := positions[a[i] := pre + {i}];
      cnt := cnt[a[i] := cnt[a[i]] + 1];
    } else {
      positions := positions[a[i] := {i}];
      cnt := cnt[a[i] := 1];
    }
    i := i + 1;
  }
  var maxCount := cnt[a[0]];
  biggest := map[a[0] := maxCount];
  i := 1;
  while i < |a|
    // invariants-start
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |a| ==> a[j] in cnt
    invariant forall j :: 0 <= j < i ==> a[j] in cnt && maxCount >= cnt[a[j]]
    invariant exists j :: 0 <= j < i && a[j] in cnt && cnt[a[j]] == maxCount
    invariant forall j :: 0 <= j < i ==> cnt[a[j]] == maxCount ==> a[j] in biggest
    invariant forall x :: x in biggest ==> x in cnt && cnt[x] == maxCount
    invariant forall x :: x in biggest ==> biggest[x] == cnt[x]
    // invariants-end
  {
    if cnt[a[i]] > maxCount {
      maxCount := cnt[a[i]];
      biggest := map[a[i] := maxCount];
    } else if cnt[a[i]] == maxCount {
      biggest := biggest[a[i] := maxCount];
    }
    i := i + 1;
  }
  // impl-end
}
