// <vc-preamble>
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): inductive snoc lemma for sum */
lemma SumSnoc(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| == 0 {
    assert |s + [x]| != 0;
    assert sum(s + [x]) == (s + [x])[0] + sum((s + [x])[1..]);
    assert (s + [x])[0] == x;
    assert |(s + [x])[1..]| == 0;
    assert sum((s + [x])[1..]) == 0;
    assert sum(s) == 0;
  } else {
    SumSnoc(s[1..], x);
    assert |s + [x]| != 0;
    assert sum(s + [x]) == (s + [x])[0] + sum((s + [x])[1..]);
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    assert sum((s + [x])[1..]) == sum(s[1..] + [x]);
    assert sum(s[1..] + [x]) == sum(s[1..]) + x;
    assert sum(s) == s[0] + sum(s[1..]);
  }
}

/* helper modified by LLM (iteration 4): inductive snoc lemma for product */
lemma ProdSnoc(s: seq<int>, x: int)
  ensures prod(s + [x]) == prod(s) * x
  decreases |s|
{
  if |s| == 0 {
    assert |s + [x]| != 0;
    assert prod(s + [x]) == (s + [x])[0] * prod((s + [x])[1..]);
    assert (s + [x])[0] == x;
    assert |(s + [x])[1..]| == 0;
    assert prod((s + [x])[1..]) == 1;
    assert prod(s) == 1;
  } else {
    ProdSnoc(s[1..], x);
    assert |s + [x]| != 0;
    assert prod(s + [x]) == (s + [x])[0] * prod((s + [x])[1..]);
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    assert prod((s + [x])[1..]) == prod(s[1..] + [x]);
    assert prod(s[1..] + [x]) == prod(s[1..]) * x;
    assert prod(s) == s[0] * prod(s[1..]);
  }
}

/* helper modified by LLM (iteration 4): sequence prefix snoc equality */
lemma PrefixSnoc(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures s[..i] + [s[i]] == s[..i+1]
{
}

/* helper modified by LLM (iteration 4): full-prefix equals the sequence */
lemma PrefixFull<T>(s: seq<T>)
  ensures s[..|s|] == s
{
}
// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)

    ensures s == sum(numbers)
    ensures p == prod(numbers)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): iterative computation with loop invariants using snoc lemmas */
{
  var i := 0;
  s := 0;
  p := 1;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant s == sum(numbers[..i])
    invariant p == prod(numbers[..i])
    decreases |numbers| - i
  {
    var oldI := i;
    var x := numbers[i];
    s := s + x;
    p := p * x;
    i := i + 1;
    SumSnoc(numbers[..oldI], x);
    ProdSnoc(numbers[..oldI], x);
    PrefixSnoc(numbers, oldI);
  }
  PrefixFull(numbers);
}
// </vc-code>
