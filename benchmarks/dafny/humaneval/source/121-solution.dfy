method solution(numbers: seq<int>) returns (s: int)
  // post-conditions-start
  ensures s == sum(numbers, seq(|numbers|, i requires 0 <= i < |numbers| => i % 2 == 0 && numbers[i] % 2 == 1))
  // post-conditions-end
{
  // impl-start
  var i := 0;
  s := 0;
  ghost var p := [];
  while i < |numbers|
    // invariants-start
    invariant 0 <= i <= |numbers|
    invariant |p| == i
    invariant s == sum(numbers[..i], p[..i])
    invariant p == seq(i, j requires 0 <= j < i => j % 2 == 0 && numbers[j] % 2 == 1)
    // invariants-end
  {
    ghost var old_p := p;
    p := p + [i % 2 == 0 && numbers[i] % 2 == 1];

    // assert-start
    assert sum(numbers[..i], p[..i]) == sum(numbers[..i], old_p[..i]) by {
      assert p[..i] == old_p[..i];
    }
    // assert-end
    // assert-start
    assert sum(numbers[..i + 1], p[..i + 1]) == sum(numbers[..i], p[..i]) + (if p[i] then numbers[i] else 0) by {
      assert numbers[..i+1][..i] == numbers[..i];
      assert p[..i + 1][..i] == p[..i] by {
        assert forall j :: 0 <= j < i ==> p[..i + 1][j] == p[..i][j];
      }
      sum_prop(numbers[..i + 1], p[..i + 1]);
    }
    // assert-end
    s := s + (if i % 2 == 0 && numbers[i] % 2 == 1 then numbers[i] else 0);

    i := i + 1;
  }
  assert numbers[..|numbers|] == numbers; // assert-line
  assert p[..|p|] == p; // assert-line
  // impl-end
}

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end
lemma sum_prop(s: seq<int>, p: seq<bool>)
  requires |s| > 0
  requires |p| == |s|
  ensures sum(s, p) == sum(s[..|s| - 1], p[..|s| - 1]) + (if p[|s| - 1] then s[|s| - 1] else 0)
{
  if (|s| > 1) {
      assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
      assert (p[1..][..|p[1..]| - 1]) == p[1..|p| - 1];
  }
}
// pure-end
