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
  var freq: map<int, int> := map[];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: freq.Contains(k) ==> freq[k] == |set j | 0 <= j < i && a[j] == k|
    invariant forall k :: exists j :: 0 <= j < i && a[j] == k ==> freq.Contains(k)
  {
    var value := a[i];
    freq := freq[value := if freq.Contains(value) then freq[value] + 1 else 1];
    i := i + 1;
  }
  
  var maxCount := 0;
  for key in freq.Keys {
    if freq[key] > maxCount {
      maxCount := freq[key];
    }
  }
  
  var biggest: BiggestMap := map[];
  for key in freq.Keys {
    if freq[key] == maxCount {
      biggest := biggest[key := maxCount];
    }
  }
  
  big := biggest;
}
// </vc-code>

