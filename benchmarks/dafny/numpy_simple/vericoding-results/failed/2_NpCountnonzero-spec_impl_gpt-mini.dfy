// <vc-preamble>
function nonzero_helper(arr: seq<real>): nat 
    decreases |arr|
{
    if |arr| == 0 then
        0
    else
        var rest_count := nonzero_helper(arr[1..]);
        if arr[0] == 0.0 then
            rest_count
        else
            rest_count + 1
}
// </vc-preamble>

// <vc-helpers>
lemma NonzeroHelperLe(s: seq<real>)
    ensures nonzero_helper(s) <= |s|
    decreases |s|
{
    if |s| == 0 { }
    else {
        NonzeroHelperLe(s[1..]);
        if s[0] == 0.0 {
            assert nonzero_helper(s) == nonzero_helper(s[1..]);
            assert nonzero_helper(s) <= |s|;
        } else {
            assert nonzero_helper(s) == nonzero_helper(s[1..]) + 1;
            assert nonzero_helper(s[1..]) <= |s[1..]|;
            assert |s[1..]| + 1 == |s|;
            assert nonzero_helper(s) <= |s|;
        }
    }
}

lemma NonzeroHelperFirstZero(s: seq<real>)
    requires |s| > 0 && s[0] == 0.0
    ensures nonzero_helper(s) == nonzero_helper(s[1..])
    decreases |s|
{
    assert nonzero_helper(s) == nonzero_helper(s[1..]);
}

/* helper modified by LLM (iteration 5): relates nonzero_helper when first element is non-zero */
lemma NonzeroHelperFirstNonzero(s: seq<real>)
    requires |s| > 0 && s[0] != 0.0
    ensures nonzero_helper(s) == nonzero_helper(s[1..]) + 1
    decreases |s|
{
    // By unfolding the definition of nonzero_helper: when s[0] != 0.0 the result is rest + 1
    assert nonzero_helper(s) == (if s[0] == 0.0 then nonzero_helper(s[1..]) else nonzero_helper(s[1..]) + 1);
    assert s[0] != 0.0;
    assert nonzero_helper(s) == nonzero_helper(s[1..]) + 1;
}

/* helper modified by LLM (iteration 5): relates nonzero_helper when appending one element */
lemma NonzeroHelperAppend(s: seq<real>, x: real)
    ensures nonzero_helper(s + [x]) == nonzero_helper(s) + (if x == 0.0 then 0 else 1)
    decreases |s|
{
    if |s| == 0 {
        if x == 0.0 {
            assert nonzero_helper([x]) == 0;
        } else {
            assert nonzero_helper([x]) == 1;
        }
    } else {
        var h := s[0];
        var t := s[1..];
        NonzeroHelperAppend(t, x);
        assert (s + [x])[1..] == t + [x];
        if h == 0.0 {
            assert nonzero_helper(s + [x]) == nonzero_helper((s + [x])[1..]);
            assert nonzero_helper((s + [x])[1..]) == nonzero_helper(t + [x]);
            assert nonzero_helper(t + [x]) == nonzero_helper(t) + (if x == 0.0 then 0 else 1);
            assert nonzero_helper(s) == nonzero_helper(t);
            assert nonzero_helper(s + [x]) == nonzero_helper(s) + (if x == 0.0 then 0 else 1);
        } else {
            assert nonzero_helper(s + [x]) == nonzero_helper((s + [x])[1..]) + 1;
            assert nonzero_helper((s + [x])[1..]) == nonzero_helper(t + [x]);
            assert nonzero_helper(t + [x]) == nonzero_helper(t) + (if x == 0.0 then 0 else 1);
            assert nonzero_helper(s) == nonzero_helper(t) + 1;
            assert nonzero_helper(s + [x]) == nonzero_helper(s) + (if x == 0.0 then 0 else 1);
        }
    }
}

// </vc-helpers>

// <vc-spec>
method nonzero(arr: array<real>) returns (result: int)
    ensures 
        result <= arr.Length &&
        result == nonzero_helper(arr[..]) &&
        (arr.Length > 0 && arr[0] == 0.0 ==> 
            nonzero_helper(arr[1..]) == if result > 0 then result - 1 else 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): count non-zero elements using helper lemmas and prove postconditions */
  var i := 0;
  result := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result == nonzero_helper(arr[..i])
  {
    var oldi := i;
    var ai := arr[oldi];
    NonzeroHelperAppend(arr[..oldi], ai);
    i := oldi + 1;
    assert arr[..i] == arr[..oldi] + [ai];
    assert nonzero_helper(arr[..i]) == nonzero_helper(arr[..oldi]) + (if ai == 0.0 then 0 else 1);
    if ai != 0.0 {
      result := result + 1;
    }
    assert result == nonzero_helper(arr[..i]);
  }
  // Post-loop: prove ensures
  assert result == nonzero_helper(arr[..]);
  NonzeroHelperLe(arr[..]);
  // Prove conditional about first element when it is non-zero
  if arr.Length > 0 && arr[0] != 0.0 {
    NonzeroHelperFirstNonzero(arr[..]);
    assert result == nonzero_helper(arr[..]);
    assert result > 0;
    assert nonzero_helper(arr[1..]) == result - 1;
  }
}

// </vc-code>
