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
        // sum(t[..1]) == t[0] + sum(t[1..1]) == t[0]
        assert (t[..1])[0] == t[0];
        assert (t[..1])[1..] == t[1..1];
        assert sum(t[..1]) == (t[..1])[0] + sum((t[..1])[1..]);
        assert sum(t[..0]) == 0;
        assert sum(t[..1]) == sum(t[..0]) + t[0];
    } else {
        // Use induction on the tail
        SumPrefixStep(t[1..], k-1);
        // Expand sums using the definition
        assert (t[..k+1])[0] == t[0];
        assert (t[..k+1])[1..] == t[1..k+1];
        assert sum(t[..k+1]) == (t[..k+1])[0] + sum((t[..k+1])[1..]);
        assert (t[..k])[0] == t[0];
        assert (t[..k])[1..] == t[1..k];
        assert sum(t[..k]) == (t[..k])[0] + sum((t[..k])[1..]);
        // From recursive call: sum(t[1..k+1]) == sum(t[1..k]) + t[k]
        assert sum(t[1..k+1]) == sum(t[1..k]) + t[k];
        // Combine to get the desired equality
        assert sum(t[..k+1]) == t[0] + sum(t[1..k+1]);
        assert sum(t[..k]) == t[0] + sum(t[1..k]);
        assert sum(t[..k+1]) == sum(t[..k]) + t[k];
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
    // element equality between computed value and square_seq entry
    assert square_seq(lst)[i] == v;
    // show prefix sum step
    SumPrefixStep(square_seq(lst), i);
    r := r + v;
    i := i + 1;
  }
}
// </vc-code>

