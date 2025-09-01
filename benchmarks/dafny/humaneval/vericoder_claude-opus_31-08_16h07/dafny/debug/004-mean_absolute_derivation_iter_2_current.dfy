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
  } else if i == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
  } else {
    calc {
      sum(s[..i]) + sum(s[i..]);
      == { assert s[..i] == s[..i-1] + [s[i-1]]; }
      sum(s[..i-1]) + s[i-1] + sum(s[i..]);
      == { sum_property(s, i-1); }
      sum(s[..i-1]) + sum(s[i-1..]);
      == { assert s[i-1..] == [s[i-1]] + s[i..]; }
      sum(s[..i-1]) + sum([s[i-1]] + s[i..]);
      == { assert sum([s[i-1]] + s[i..]) == s[i-1] + sum(s[i..]); }
      sum(s[..i-1]) + s[i-1] + sum(s[i..]);
      == { sum_property(s, i-1); }
      sum(s);
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

