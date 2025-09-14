

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method below_zero(operations: seq<int>) returns (s:array<int>, result:bool)
  ensures s.Length == |operations| + 1
  ensures s[0]==0
  ensures forall i :: 0 <= i < s.Length-1 ==> s[i+1]==s[i]+operations[i]
  ensures result == true ==> (exists i :: 1 <= i <= |operations| && s[i] < 0)
  ensures result == false ==> forall i :: 0 <= i < s.Length ==> s[i] >= 0
// </vc-spec>
// <vc-code>
{
  var n := |operations|;
  s := new int[n + 1];
  s[0] := 0;
  var found := false;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s.Length == n + 1
    invariant s[0] == 0
    invariant forall j :: 0 <= j < i ==> s[j+1] == s[j] + operations[j]
    invariant found == (exists k :: 1 <= k <= i && s[k] < 0)
  {
    var oldFound := found;
    assert oldFound == (exists k :: 1 <= k <= i && s[k] < 0);
    s[i+1] := s[i] + operations[i];
    if s[i+1] < 0 {
      found := true;
      // witness i+1 shows existence up to i+1
      assert exists k :: 1 <= k <= i+1 && s[k] < 0;
    } else {
      found := oldFound;
      if oldFound {
        // extract witness from the old existence (which ranges up to i)
        var k :| 1 <= k <= i && s[k] < 0;
        assert 1 <= k <= i+1 && s[k] < 0;
        assert exists k2 :: 1 <= k2 <= i+1 && s[k2] < 0;
      } else {
        // no witness in 1..i and s[i+1] >= 0, so none in 1..i+1
        assert !(exists k :: 1 <= k <= i+1 && s[k] < 0);
      }
    }
    i := i + 1;
  }
  result := found;
}
// </vc-code>

