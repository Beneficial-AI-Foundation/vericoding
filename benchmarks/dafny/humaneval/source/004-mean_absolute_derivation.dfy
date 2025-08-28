function sum(s: seq<real>) : real {
  if |s| == 0 then 0.0 else s[0] + sum(s[1..])
}
// pure-end
lemma sum_prop(s: seq<real>)
  requires |s| > 0
  ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
  if (|s| > 1) {
    assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
  }
}
// pure-end
function abs(x: real) : real
  ensures abs(x) >= 0.0
{
  if x >= 0.0 then x else -x
}
// pure-end
function mean(s: seq<real>) : real
  requires |s| > 0
{
  sum(s) / |s| as real
}
// pure-end
method mean_absolute_derivation(numbers: seq<real>) returns (derivation: real)
  // pre-conditions-start
  requires |numbers| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures var m := mean(numbers);
    derivation == mean(seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m)))
  // post-conditions-end
{
  // impl-start
  var s: real := 0.0;
  for i := 0 to |numbers|
    // invariants-start
    invariant s == sum(numbers[..i])
    // invariants-end
  {
    s := s + numbers[i];
    // assert-start
    assert sum(numbers[..i + 1]) == sum(numbers[..i]) + numbers[i] by {
      assert numbers[..i+1][..i] == numbers[..i];
      sum_prop(numbers[..i + 1]);
    }
    // assert-end
  }

  var m := s / |numbers| as real;
  assert numbers[..|numbers|] == numbers; // assert-line
  assert m == mean(numbers); // assert-line

  var t: real := 0.0;

  ghost var pref_seq := [];
  for i := 0 to |numbers|
    // invariants-start
    invariant |pref_seq| == i
    invariant pref_seq == seq(i, j requires 0 <= j < i => abs(numbers[j] - m))
    invariant t == sum(pref_seq[..i])
    // invariants-end
  {
    ghost var pre_seq := pref_seq;
    assert pre_seq[..|pre_seq|] == pre_seq[..i] == pre_seq; // assert-line

    pref_seq := pref_seq + [abs(numbers[i] - m)];

    // assert-start
    assert sum(pref_seq[..i + 1]) == sum(pref_seq[..i]) + pref_seq[i] by {
      assert pref_seq[..i+1][..i] == pref_seq[..i];
      sum_prop(pref_seq[..i + 1]);
    }
    // assert-end

    t := t + abs(numbers[i] - m);
  }

  assert pref_seq[..|pref_seq|] == pref_seq; // assert-line
  derivation := t / |numbers| as real;
  // impl-end
}
