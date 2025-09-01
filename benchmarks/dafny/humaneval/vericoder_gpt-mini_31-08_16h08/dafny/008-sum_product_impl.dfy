function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
lemma SumCons(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures sum(s[..k+1]) == sum(s[..k]) + s[k]
  decreases k
{
  if k == 0 {
    assert sum(s[..1]) == (s[..1])[0] + sum((s[..1])[1..]);
    assert (s[..1])[0] == s[0];
    assert (s[..1])[1..] == s[1..1];
    assert sum(s[1..1]) == 0;
    assert sum(s[..0]) == 0;
    assert sum(s[..1]) == s[0] + 0;
    assert s[0] + 0 == sum(s[..0]) + s[0];
  } else {
    SumCons(s[1..], k-1);
    // relate prefixes of the tail to slices of the original
    assert (s[1..])[..k] == s[1..k+1];
    assert (s[1..])[..k-1] == s[1..k];
    assert (s[1..])[k-1] == s[k];
    // use the recursive result
    assert sum(s[1..k+1]) == sum(s[1..k]) + s[k];

    // expand sums of prefixes of original sequence
    assert sum(s[..k+1]) == (s[..k+1])[0] + sum((s[..k+1])[1..]);
    assert (s[..k+1])[0] == s[0];
    assert (s[..k+1])[1..] == s[1..k+1];
    assert sum(s[..k+1]) == s[0] + sum(s[1..k+1]);

    assert sum(s[..k]) == (s[..k])[0] + sum((s[..k])[1..]);
    assert (s[..k])[0] == s[0];
    assert (s[..k])[1..] == s[1..k];
    assert sum(s[..k]) == s[0] + sum(s[1..k]);

    assert sum(s[..k+1]) == s[0] + (sum(s[1..k]) + s[k]);
    assert s[0] + (sum(s[1..k]) + s[k]) == (s[0] + sum(s[1..k])) + s[k];
    assert (s[0] + sum(s[1..k])) == sum(s[..k]);
  }
}

lemma ProdCons(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures prod(s[..k+1]) == prod(s[..k]) * s[k]
  decreases k
{
  if k == 0 {
    assert prod(s[..1]) == (s[..1])[0] * prod((s[..1])[1..]);
    assert (s[..1])[0] == s[0];
    assert (s[..1])[1..] == s[1..1];
    assert prod(s[1..1]) == 1;
    assert prod(s[..0]) == 1;
    assert prod(s[..1]) == s[0] * 1;
    assert s[0] * 1 == prod(s[..0]) * s[0];
  } else {
    ProdCons(s[1..], k-1);

    assert (s[1..])[..k] == s[1..k+1];
    assert (s[1..])[..k-1] == s[1..k];
    assert (s[1..])[k-1] == s[k];
    assert prod(s[1..k+1]) == prod(s[1..k]) * s[k];

    assert prod(s[..k+1]) == (s[..k+1])[0] * prod((s[..k+1])[1..]);
    assert (s[..k+1])[0] == s[0];
    assert (s[..k+1])[1..] == s[1..k+1];
    assert prod(s[..k+1]) == s[0] * prod(s[1..k+1]);

    assert prod(s[..k]) == (s[..k])[0] * prod((s[..k])[1..]);
    assert (s[..k])[0] == s[0];
    assert (s[..k])[1..] == s[1..k];
    assert prod(s[..k]) == s[0] * prod(s[1..k]);

    assert prod(s[..k+1]) == s[0] * (prod(s[1..k]) * s[k]);
    assert s[0] * (prod(s[1..k]) * s[k]) == (s[0] * prod(s[1..k])) * s[k];
    assert (s[0] * prod(s[1..k])) == prod(s[..k]);
  }
}
// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)
    // post-condition-start
    ensures s == sum(numbers)
    ensures p == prod(numbers)
    // post-condition-end
// </vc-spec>
// <vc-code>
{
  s := 0;
  p := 1;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant s == sum(numbers[..i])
    invariant p == prod(numbers[..i])
    decreases |numbers| - i
  {
    var x := numbers[i];
    s := s + x;
    p := p * x;
    SumCons(numbers, i);
    ProdCons(numbers, i);
    i := i + 1;
  }
  assert i == |numbers|;
  assert numbers[..i] == numbers;
  assert s == sum(numbers);
  assert p == prod(numbers);
}
// </vc-code>

