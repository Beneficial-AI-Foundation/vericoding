// <vc-preamble>
function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): robust concat lemma with explicit base case reasoning */
lemma CountRecConcat(s1: seq<int>, s2: seq<int>, x: int)
  ensures count_rec(s1 + s2, x) == count_rec(s1, x) + count_rec(s2, x)
  decreases |s1|
{
  if |s1| == 0 {
    assert s1 == [];
    assert s1 + s2 == s2;
    assert count_rec(s1, x) == 0;
    assert count_rec(s1 + s2, x) == count_rec(s2, x);
    assert count_rec(s1 + s2, x) == count_rec(s1, x) + count_rec(s2, x);
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    CountRecConcat(s1[1..], s2, x);
    assert count_rec(s1 + s2, x) ==
           count_rec((s1 + s2)[1..], x) + (if (s1 + s2)[0] == x then 1 else 0);
    assert count_rec(s1 + s2, x) ==
           count_rec(s1[1..] + s2, x) + (if s1[0] == x then 1 else 0);
    assert count_rec(s1[1..] + s2, x) == count_rec(s1[1..], x) + count_rec(s2, x);
    assert count_rec(s1, x) ==
           count_rec(s1[1..], x) + (if s1[0] == x then 1 else 0);
    assert count_rec(s1 + s2, x) == count_rec(s1, x) + count_rec(s2, x);
  }
}

/* helper modified by LLM (iteration 5): single-element sequence evaluation for count_rec */
lemma CountRecOne(v: int, x: int)
  ensures count_rec([v], x) == (if v == x then 1 else 0)
{
  assert ([v])[1..] == [];
  assert ([v])[0] == v;
  assert count_rec([v], x) == count_rec(([v])[1..], x) + (if ([v])[0] == x then 1 else 0);
  assert count_rec([], x) == 0;
}

/* helper modified by LLM (iteration 5): counting step when appending one element */
lemma CountRecPrefixStep(s: seq<int>, v: int, x: int)
  ensures count_rec(s + [v], x) == count_rec(s, x) + (if v == x then 1 else 0)
{
  CountRecConcat(s, [v], x);
  CountRecOne(v, x);
  assert count_rec([v], x) == (if v == x then 1 else 0);
  assert count_rec(s + [v], x) == count_rec(s, x) + count_rec([v], x);
}

/* helper modified by LLM (iteration 5): relate recursive count to set cardinality with finite-empty base case */
lemma CountRecEqualsSetCard(s: seq<int>, x: int)
  ensures count_rec(s, x) == |set i | 0 <= i < |s| && s[i] == x|
  decreases |s|
{
  if |s| == 0 {
    assert (set i | 0 <= i < |s| && s[i] == x) == {};
    assert count_rec(s, x) == 0;
  } else {
    var t := s[..|s|-1];
    var v := s[|s|-1];
    assert s == t + [v];

    CountRecEqualsSetCard(t, x);
    CountRecPrefixStep(t, v, x);

    assert (set i | 0 <= i < |s| && s[i] == x) ==
           (set i | 0 <= i < |t| + 1 && (t + [v])[i] == x);

    if v == x {
      assert (set i | 0 <= i < |t| + 1 && (t + [v])[i] == x) ==
             (set i | 0 <= i < |t| && t[i] == x) + { |t| };
      assert |t| !in (set i | 0 <= i < |t| && t[i] == x);
      assert |set i | 0 <= i < |s| && s[i] == x| == |set i | 0 <= i < |t| && t[i] == x| + 1;
      assert count_rec(s, x) == count_rec(t, x) + 1;
      assert count_rec(t, x) == |set i | 0 <= i < |t| && t[i] == x|;
    } else {
      assert (set i | 0 <= i < |t| + 1 && (t + [v])[i] == x) ==
             (set i | 0 <= i < |t| && t[i] == x);
      assert |set i | 0 <= i < |s| && s[i] == x| == |set i | 0 <= i < |t| && t[i] == x|;
      assert count_rec(s, x) == count_rec(t, x);
      assert count_rec(t, x) == |set i | 0 <= i < |t| && t[i] == x|;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>, x: int) returns (cnt: int)

  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): strengthened loop proof and post-loop equivalence */
  var i := 0;
  cnt := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant cnt == count_rec(a[..i], x)
    decreases |a| - i
  {
    if a[i] == x {
      cnt := cnt + 1;
      CountRecPrefixStep(a[..i], a[i], x);
      assert a[..i] + [a[i]] == a[..i+1];
      assert cnt == count_rec(a[..i+1], x);
    } else {
      CountRecPrefixStep(a[..i], a[i], x);
      assert a[..i] + [a[i]] == a[..i+1];
      assert cnt == count_rec(a[..i+1], x);
    }
    i := i + 1;
  }
  assert i == |a|;
  assert a[..i] == a;
  assert cnt == count_rec(a, x);
  CountRecEqualsSetCard(a, x);
  assert cnt == |set i | 0 <= i < |a| && a[i] == x|;
}
// </vc-code>
