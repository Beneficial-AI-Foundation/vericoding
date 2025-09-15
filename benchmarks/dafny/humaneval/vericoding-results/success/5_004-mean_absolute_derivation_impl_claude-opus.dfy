function sum(s: seq<real>) : real {
  if |s| == 0 then 0.0 else s[0] + sum(s[1..])
}
function abs(x: real) : real
  ensures abs(x) >= 0.0
{
  if x >= 0.0 then x else -x
}
function mean(s: seq<real>) : real
  requires |s| > 0
{
  sum(s) / |s| as real
}

// <vc-helpers>
lemma sum_property(s: seq<real>, i: nat)
  requires 0 <= i <= |s|
  ensures sum(s[..i]) + sum(s[i..]) == sum(s)
{
  if i == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
    assert sum([]) == 0.0;
    assert sum(s[..0]) + sum(s[0..]) == 0.0 + sum(s) == sum(s);
  } else if i == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
    assert sum([]) == 0.0;
    assert sum(s[..|s|]) + sum(s[|s|..]) == sum(s) + 0.0 == sum(s);
  } else if |s| > 0 {
    assert s == [s[0]] + s[1..];
    calc {
      sum(s);
      == // by definition of sum
      s[0] + sum(s[1..]);
      == { sum_property(s[1..], i-1); }
      s[0] + (sum(s[1..][..i-1]) + sum(s[1..][i-1..]));
      == { assert s[1..][..i-1] == s[1..i]; assert s[1..][i-1..] == s[i..]; }
      s[0] + sum(s[1..i]) + sum(s[i..]);
      == { assert s[..i] == [s[0]] + s[1..i]; sum_concat([s[0]], s[1..i]); }
      sum(s[..i]) + sum(s[i..]);
    }
  }
}

lemma sum_concat(s1: seq<real>, s2: seq<real>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    calc {
      sum(s1 + s2);
      == // by definition, since |s1| > 0 implies |s1 + s2| > 0
      (s1 + s2)[0] + sum((s1 + s2)[1..]);
      == { assert (s1 + s2)[0] == s1[0]; assert (s1 + s2)[1..] == s1[1..] + s2; }
      s1[0] + sum(s1[1..] + s2);
      == { sum_concat(s1[1..], s2); }
      s1[0] + sum(s1[1..]) + sum(s2);
      == // by definition of sum
      sum(s1) + sum(s2);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method mean_absolute_derivation(numbers: seq<real>) returns (derivation: real)
  // pre-conditions-start
  requires |numbers| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures var m := mean(numbers);
    derivation == mean(seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m)))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var m := mean(numbers);
  var diffs := seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m));
  derivation := mean(diffs);
}
// </vc-code>

