type BiggestMap = map<int, int>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method count(a: seq<int>) returns (biggest: BiggestMap)
  // post-conditions-start
  ensures forall i :: 0 <= i < |a| && a[i] in biggest ==>
    biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==>
    biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==>
    biggest[a[i]] == biggest[a[j]]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var freq: map<int,int> := map[];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|;
    invariant forall x :: x in freq ==>
      freq[x] == |set j | 0 <= j < i && a[j] == x|;
    invariant forall x :: x in freq ==> freq[x] >= 1;
  {
    var v := a[i];
    if v in freq {
      freq := freq[v := freq[v] + 1];
    } else {
      freq := freq[v := 1];
    }
    i := i + 1;
  }

  var maxCount := 0;
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|;
    invariant forall t :: 0 <= t < j ==> maxCount >= freq[a[t]];
  {
    var v := a[j];
    if freq[v] > maxCount {
      maxCount := freq[v];
    }
    j := j + 1;
  }

  biggest := map k | k in freq && freq[k] == maxCount :: maxCount;
}
// </vc-code>

