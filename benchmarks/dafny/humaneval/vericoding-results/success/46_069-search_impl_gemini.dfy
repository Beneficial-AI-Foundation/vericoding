// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)

    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed compilation error in set construction */
{
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |set j | 0 <= j < i && s[j] == x|
  {
    var set_upto_i := set j | 0 <= j < i && s[j] == x;
    var set_at_i := if s[i] == x then {i} else {};
    var set_upto_i_plus_1 := set j | 0 <= j < i + 1 && s[j] == x;
    assert set_upto_i_plus_1 == set_upto_i + set_at_i;
    assert set_upto_i !! set_at_i;

    if s[i] == x {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
