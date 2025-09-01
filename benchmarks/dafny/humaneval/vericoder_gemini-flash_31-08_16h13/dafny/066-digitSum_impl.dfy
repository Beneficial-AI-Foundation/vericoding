function upper_sum_rec(s: string): int
  // post-conditions-start
  ensures upper_sum_rec(s) >= 0
  // post-conditions-end
{
  // impl-start
  if |s| == 0 then
    0
  else
    var remaining := upper_sum_rec(s[1..]);
    to_int(s[0]) + remaining
  // impl-end
}
function to_int(c: char): int
    ensures 'A' <= c <= 'Z' ==> to_int(c) == c as int
    ensures c < 'A' || c > 'Z' ==> to_int(c) == 0
{
    if 'A' <= c <= 'Z' then c as int else 0
}

// <vc-helpers>
function upper_sum_rec_iter(s: string, i: int): int
    requires 0 <= i <= |s|
    ensures upper_sum_rec_iter(s, i) >= 0
    decreases |s| - i
{
    if i == |s| then
        0
    else
        to_int(s[i]) + upper_sum_rec_iter(s, i + 1)
}

lemma SumProperty(s: string, i: int)
    requires 0 <= i <= |s|
    ensures upper_sum_rec(s[i..]) == upper_sum_rec_iter(s, i)
    decreases |s| - i
{
    if i < |s| {
        calc {
            upper_sum_rec(s[i..]);
            to_int(s[i]) + upper_sum_rec(s[i+1..]);
            { SumProperty(s, i+1); }
            to_int(s[i]) + upper_sum_rec_iter(s, i+1);
            upper_sum_rec_iter(s, i);
        }
    } else {
      assert i == |s|;
      assert upper_sum_rec(s[i..]) == 0;
      assert upper_sum_rec_iter(s, i) == 0;
    }
}

lemma SumPrefixSuffix(s: string, i: int)
    requires 0 <= i <= |s|
    ensures upper_sum_rec(s) == upper_sum_rec(s[0..i]) + upper_sum_rec(s[i..])
    decreases i
{
    if i == 0 {
        assert upper_sum_rec(s[0..0]) == 0;
        assert upper_sum_rec(s[0..i]) == 0;
        assert upper_sum_rec(s[i..]) == upper_sum_rec(s);
    } else if i == |s| {
        assert upper_sum_rec(s[|s|..|s|]) == 0;
        assert upper_sum_rec(s[i..]) == 0;
        assert s[0..i] == s; // This is a property of slicing in Dafny
        assert upper_sum_rec(s[0..i]) == upper_sum_rec(s);
    } else {
        // This is the recursive step
        calc {
            upper_sum_rec(s);
            to_int(s[0]) + upper_sum_rec(s[1..]);
            { SumPrefixSuffix(s[1..], i-1); }
            to_int(s[0]) + (upper_sum_rec(s[1..i]) + upper_sum_rec(s[i..]));
            (to_int(s[0]) + upper_sum_rec(s[1..i])) + upper_sum_rec(s[i..]);
            upper_sum_rec(s[0]) + upper_sum_rec(s[1..i]);
            upper_sum_rec(s[0..i]) + upper_sum_rec(s[i..]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method upper_sum(s: string) returns (res: int)
    // post-conditions-start
    ensures res == upper_sum_rec(s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var sum := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant sum == upper_sum_rec(s[0..i])
        decreases |s| - i
    {
        sum := sum + to_int(s[i]);
        assert upper_sum_rec(s[0..i+1]) == upper_sum_rec(s[0..i]) + to_int(s[i]);
        i := i + 1;
    }
    assert i == |s|;
    assert s[0..i] == s;
    assert sum == upper_sum_rec(s);
    return sum;
}
// </vc-code>

