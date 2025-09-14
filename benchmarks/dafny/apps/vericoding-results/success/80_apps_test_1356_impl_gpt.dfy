function count_a(s: string): int
    ensures count_a(s) >= 0
    ensures count_a(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == 'a' then 1 else 0) + count_a(s[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

predicate ValidInput(s: string)
{
    |s| >= 1 && exists i :: 0 <= i < |s| && s[i] == 'a'
}

predicate IsGoodString(s: string)
{
    |s| > 0 && count_a(s) > |s| / 2
}

// <vc-helpers>
lemma CountA_AtLeastOne(s: string)
  requires exists i :: 0 <= i < |s| && s[i] == 'a'
  ensures count_a(s) >= 1
  decreases |s|
{
  var iWitness :| 0 <= iWitness < |s| && s[iWitness] == 'a';
  assert |s| > 0;
  assert count_a(s) == (if s[0] == 'a' then 1 else 0) + count_a(s[1..]);
  if s[0] == 'a' {
    assert count_a(s) == 1 + count_a(s[1..]);
    assert count_a(s[1..]) >= 0;
  } else {
    assert iWitness > 0;
    var j := iWitness - 1;
    assert 0 <= j < |s[1..]|;
    assert j + 1 == iWitness;
    assert s[1..][j] == s[j + 1];
    assert s[1..][j] == s[iWitness];
    assert s[1..][j] == 'a';
    assert exists k :: 0 <= k < |s[1..]| && s[1..][k] == 'a';
    CountA_AtLeastOne(s[1..]);
    assert count_a(s) == count_a(s[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 1
    ensures result <= |s|
    ensures result == min(2 * count_a(s) - 1, |s|)
// </vc-spec>
// <vc-code>
{
  CountA_AtLeastOne(s);
  result := min(2 * count_a(s) - 1, |s|);
}
// </vc-code>

