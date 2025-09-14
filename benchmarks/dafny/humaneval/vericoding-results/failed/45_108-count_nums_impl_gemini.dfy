// <vc-preamble>
function digits_sum(x: int): int
  decreases abs(x)
{
  if abs(x) < 10 then x else x % 10 + digits_sum(x / 10)
}
function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
function CountSet(s: seq<int>, k: nat): set<nat>
  requires k <= |s|
{
  set j | 0 <= j < k && digits_sum(s[j]) > 0
}

/* helper modified by LLM (iteration 4): implemented proof for the set cardinality update */
lemma CountSetUpdate(s: seq<int>, i: nat)
  requires i < |s|
  ensures |CountSet(s, i + 1)| == |CountSet(s, i)| + (if digits_sum(s[i]) > 0 then 1 else 0)
{
  if digits_sum(s[i]) > 0 {
    assert CountSet(s, i + 1) == CountSet(s, i) + {i};
    assert i !in CountSet(s, i);
  } else {
    assert CountSet(s, i + 1) == CountSet(s, i);
  }
}
// </vc-helpers>

// <vc-spec>
method count_nums(s: seq<int>) returns (cnt: nat)

  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): unchanged, relies on fixed helper lemma */
  cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |CountSet(s, i)|
  {
    CountSetUpdate(s, i);
    if digits_sum(s[i]) > 0 {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
