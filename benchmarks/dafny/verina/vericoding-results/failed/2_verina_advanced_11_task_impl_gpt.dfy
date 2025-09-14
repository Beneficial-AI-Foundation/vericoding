// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
lemma CountPositiveImpliesExists(x: int, s: seq<int>)
  ensures CountOccurrences(x, s) > 0 ==> exists i :: 0 <= i < |s| && s[i] == x
{ }

lemma MajorityUnique(s: seq<int>, y: int)
  ensures CountOccurrences(y, s) > |s|/2 ==> forall x :: CountOccurrences(x, s) <= |s|/2 || x == y
{ }
// </vc-helpers>

// <vc-spec>
method FindMajorityElement(lst: array<int>) returns (result: int)
    ensures var lst_seq := lst[..];
            var n := |lst_seq|;
            var majority := CountOccurrences(result, lst_seq) > n / 2 && 
                          forall x :: CountOccurrences(x, lst_seq) <= n / 2 || x == result;
            (result == -1 ==> forall x :: CountOccurrences(x, lst_seq) <= n / 2) &&
            (result != -1 ==> majority)
// </vc-spec>
// <vc-code>
{
  var s := lst[..];
  var n := |s|;
  var half := n / 2;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> CountOccurrences(s[j], s) <= half
  {
    if CountOccurrences(s[i], s) > half {
      result := s[i];
      MajorityUnique(s, result);
      return;
    }
    i := i + 1;
  }
  result := -1;
  assert forall x :: CountOccurrences(x, s) <= half
  {
    if CountOccurrences(x, s) > 0 {
      CountPositiveImpliesExists(x, s);
      var j :| 0 <= j < n && s[j] == x;
      assert CountOccurrences(s[j], s) <= half;
      assert x == s[j];
      assert CountOccurrences(x, s) == CountOccurrences(s[j], s);
      assert CountOccurrences(x, s) <= half;
    }
  }
}
// </vc-code>
