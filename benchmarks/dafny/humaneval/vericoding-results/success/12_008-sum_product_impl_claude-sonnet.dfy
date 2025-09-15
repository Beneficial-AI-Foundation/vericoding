// <vc-preamble>
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemmas to prove sum and prod properties for loop invariants */
lemma SumAppend(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert sum([x]) == x + sum([]);
    assert sum([]) == 0;
  } else {
    assert s + [x] == [s[0]] + s[1..] + [x];
    assert s + [x] == [s[0]] + (s[1..] + [x]);
    SumAppend(s[1..], x);
  }
}

lemma ProdAppend(s: seq<int>, x: int)
  ensures prod(s + [x]) == prod(s) * x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert prod([x]) == x * prod([]);
    assert prod([]) == 1;
  } else {
    assert s + [x] == [s[0]] + s[1..] + [x];
    assert s + [x] == [s[0]] + (s[1..] + [x]);
    ProdAppend(s[1..], x);
  }
}
// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)

    ensures s == sum(numbers)
    ensures p == prod(numbers)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added lemma calls to prove invariant maintenance */
  s := 0;
  p := 1;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant s == sum(numbers[..i])
    invariant p == prod(numbers[..i])
  {
    assert numbers[..i+1] == numbers[..i] + [numbers[i]];
    SumAppend(numbers[..i], numbers[i]);
    ProdAppend(numbers[..i], numbers[i]);
    s := s + numbers[i];
    p := p * numbers[i];
    i := i + 1;
  }
  assert numbers[..|numbers|] == numbers;
}
// </vc-code>
