predicate ValidInput(diameters: seq<int>)
{
    |diameters| > 0 && forall i :: 0 <= i < |diameters| ==> diameters[i] > 0
}

function num_distinct(s: seq<int>): int
    ensures num_distinct(s) >= 0
    ensures num_distinct(s) <= |s|
    ensures |s| == 0 ==> num_distinct(s) == 0
    ensures |s| > 0 ==> num_distinct(s) >= 1
{
    if |s| == 0 then 0
    else if s[0] in s[1..] then num_distinct(s[1..])
    else 1 + num_distinct(s[1..])
}

// <vc-helpers>
lemma DistinctSetCount(s: seq<int>)
    ensures |set j | 0 <= j < |s| :: s[j]| == num_distinct(s)
{
    if |s| == 0 {
    } else {
        var s' := s[1..];
        DistinctSetCount(s');
        var setRest := set j | 1 <= j < |s| :: s[j];
        assert setRest == set j | 0 <= j < |s'| :: s'[j];
        var setAll := {s[0]} + setRest;
        assert setAll == set j | 0 <= j < |s| :: s[j];
        if s[0] in setRest {
            assert {s[0]} + setRest == setRest;
            assert |setAll| == |setRest|;
            assert |setRest| == num_distinct(s');
            assert num_distinct(s') == num_distinct(s);
            assert |setAll| == num_distinct(s);
        } else {
            assert |setAll| == |setRest| + 1;
            assert |setRest| == num_distinct(s');
            assert num_distinct(s) == 1 + num_distinct(s');
            assert |setAll| == num_distinct(s);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(diameters: seq<int>) returns (result: int)
    requires ValidInput(diameters)
    ensures result == num_distinct(diameters)
    ensures result >= 1
    ensures result <= |diameters|
// </vc-spec>
// <vc-code>
{
  var seen: set<int> := {};
  var i := 0;
  while i < |diameters|
      invariant 0 <= i <= |diameters|
      invariant seen == set j | 0 <= j < i :: diameters[j]
  {
      if diameters[i] in seen {
          i := i + 1;
      } else {
          seen := seen + {diameters[i]};
          i := i + 1;
      }
  }
  assert seen == set j | 0 <= j < |diameters| :: diameters[j];
  DistinctSetCount(diameters);
  return |seen|;
}
// </vc-code>

