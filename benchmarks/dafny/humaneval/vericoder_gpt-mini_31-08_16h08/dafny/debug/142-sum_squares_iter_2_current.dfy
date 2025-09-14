function sum(s: seq<int>) : int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function square_seq(lst: seq<int>) : (sq : seq<int>)
    ensures |sq| == |lst|
{
    seq(|lst|, i requires 0 <= i < |lst| => if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
}

// <vc-helpers>
lemma SumPrefixStep(t: seq<int>, k: nat)
    requires k < |t|
    ensures sum(t[..k+1]) == sum(t[..k]) + t[k]
    decreases k
{
    if k == 0 {
        // t[..1] has head t[0] and empty tail
        assert (t[..1])[0] == t[0];
        assert (t[..1])[1..] == t[1..1];
        assert sum(t[..1]) == (t[..1])[0] + sum((t[..1])[1..]);
        assert sum((t[..1])[1..]) == 0;
        assert sum(t[..0]) == 0;
        assert sum(t[..1]) == sum(t[..0]) + t[0];
    } else {
        // Apply lemma to the tail
        SumPrefixStep(t[1..], k-1);
        // From the recursive call:
        assert sum((t[1..])[..k]) == sum((t[1..])[..(k-1)]) + (t[1..])[k-1];
        // Relate slices to the original sequence
        assert (t[1..])[..k] == t[1..k+1];
        assert (t[1..])[..(k-1)] == t[1..k];
        assert (t[1..])[k-1] == t[k];
        // Substitute to get the sum over the interior slice
        assert sum(t[1..k+1]) == sum(t[1..k]) + t[k];
        // Expand sums of prefixes of t
        assert sum(t[..k+1]) == (t[..k+1])[0] + sum((t[..k+1])[1..]);
        assert (t[..k+1])[0] == t[0];
        assert (t[..k+1])[1..] == t[1..k+1];
        assert sum(t[..k]) == (t[..k])[0] + sum((t[..k])[1..]);
        assert (t[..k])[0] == t[0];
        assert (t[..k])[1..] == t[1..k];
        // Combine to conclude the step
        assert sum(t[..k+1]) == t[0] + sum(t[1..k+1]);
        assert sum(t[..k]) == t[0] + sum(t[1..k]);
        assert sum(t[..k+1]) == sum(t[..k]) + t[k];
    }
}

lemma SumFull(s: seq<int>)
    ensures sum(s) == sum(s[..|s|])
    decreases |s|
{
    if |s| == 0 {
        assert s[..0] == [];
        assert sum(s) == 0;
        assert sum(s[..0]) == 0;
    } else {
        // Expand definitions
        assert sum(s) == s[0] + sum(s[1..]);
        // Induction on the tail
        SumFull(s[1..]);
        // Relate full slice to original sequence
        assert (s[..|s|])[0] == s[0];
        assert (s[..|s|])[1..] == s[1..];
        assert sum(s[..|s|]) == (s[..|s|])[0] + sum((s[..|s|])[1..]);
        assert sum((s[..|s|])[1..]) == sum(s[1..]);
        assert sum(s[..|s|]) == s[0] + sum(s[1..]);
        assert sum(s) == sum(s[..|s|]);
    }
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant r == sum(square_seq(lst)[0..i])
  {
    var v := if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]);
    assert square_seq(lst)[i] == v;
    SumPrefixStep(square_seq(lst), i);
    r := r + v;
    i := i + 1;
  }
  SumFull(square_seq(lst));
  assert r == sum(square_seq(lst));
}
// </vc-code>

