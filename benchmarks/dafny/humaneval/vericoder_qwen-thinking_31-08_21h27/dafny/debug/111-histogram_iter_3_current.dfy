type BiggestMap = map<int, int>

// <vc-helpers>
// No changes needed in helpers as error is in code initialization
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
  var freq := map<int, int> ();
  for i := 0 to |a| - 1 {
    freq[a[i]] := freq[a[i]] + 1;
  }
  var maxCount := 0;
  if |a| > 0 {
    var values := { freq[k] | k in freq.Keys };
    maxCount := values.Max();
  }
  biggest := map k | k in freq && freq[k] == maxCount :: maxCount;
}
// </vc-code>

