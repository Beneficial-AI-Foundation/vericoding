// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added explicit triggers to fix compilation warnings */
lemma SetCardinalityLemma(s: seq<int>, i: int)
  requires 0 <= i <= |s| / 2
  ensures |set j {:trigger s[j]} | 0 <= j < i && s[j] != s[|s| - 1 - j]| == |set j {:trigger s[j]} | 0 <= j < i && s[j] != s[|s| - 1 - j]|
{
}

function CountMismatches(s: seq<int>, i: int): int
  requires 0 <= i <= |s| / 2
{
  if i == 0 then 0
  else CountMismatches(s, i - 1) + (if s[i - 1] != s[|s| - 1 - (i - 1)] then 1 else 0)
}

lemma CountMatchesCardinality(s: seq<int>, i: int)
  requires 0 <= i <= |s| / 2
  ensures CountMismatches(s, i) == |set j {:trigger s[j]} | 0 <= j < i && s[j] != s[|s| - 1 - j]|
{
  if i == 0 {
    assert (set j {:trigger s[j]} | 0 <= j < 0 && s[j] != s[|s| - 1 - j]) == {};
  } else {
    CountMatchesCardinality(s, i - 1);
    var prev_set := set j {:trigger s[j]} | 0 <= j < i - 1 && s[j] != s[|s| - 1 - j];
    var curr_set := set j {:trigger s[j]} | 0 <= j < i && s[j] != s[|s| - 1 - j];
    if s[i - 1] != s[|s| - 1 - (i - 1)] {
      assert curr_set == prev_set + {i - 1};
      assert (i - 1) !in prev_set;
      assert |curr_set| == |prev_set| + 1;
    } else {
      assert curr_set == prev_set;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)

  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Added explicit triggers to fix compilation warnings */
  c := 0;
  var i := 0;
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant c == CountMismatches(s, i)
    invariant c == |set j {:trigger s[j]} | 0 <= j < i && s[j] != s[|s| - 1 - j]|
  {
    if s[i] != s[|s| - 1 - i] {
      c := c + 1;
    }
    i := i + 1;
    CountMatchesCardinality(s, i);
  }
  CountMatchesCardinality(s, |s| / 2);
}
// </vc-code>
