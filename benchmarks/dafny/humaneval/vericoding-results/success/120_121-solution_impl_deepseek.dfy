// <vc-preamble>
function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// </vc-preamble>

// <vc-helpers>
function sum_helper(s: seq<int>, p: seq<bool>, i: int): int
  requires 0 <= i <= |s|
  requires |s| == |p|
  decreases |s| - i
{
  if i == |s| then 0 else (if p[i] then s[i] else 0) + sum_helper(s, p, i+1)
}

lemma sum_lemma(s: seq<int>, p: seq<bool>, i: int)
  requires 0 <= i <= |s|
  requires |s| == |p|
  ensures sum_helper(s, p, i) == sum(s[i..], p[i..])
  decreases |s| - i
{
  if i < |s| {
    sum_lemma(s, p, i+1);
  }
}

/* helper modified by LLM (iteration 2): Added invariant helper lemma for while loop proof */
lemma loop_invariant_helper(s: seq<int>, p: seq<bool>, j: int)
  requires 0 <= j <= |s|
  requires |s| == |p|
  ensures sum_helper(s, p, j) == sum_helper(s, p, j)
{
}
// </vc-helpers>

// <vc-spec>
method solution(numbers: seq<int>) returns (s: int)

  ensures s == sum(numbers, seq(|numbers|, i requires 0 <= i < |numbers| => i % 2 == 0 && numbers[i] % 2 == 1))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariant to use incremental approach */
  s := 0;
  var i := 0;
  var p := seq(|numbers|, j requires 0 <= j < |numbers| => j % 2 == 0 && numbers[j] % 2 == 1);
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant s == sum_helper(numbers, p, 0) - sum_helper(numbers, p, i)
  {
    var prev_s := s;
    if p[i] {
      s := s + numbers[i];
    }
    assert s == prev_s + (if p[i] then numbers[i] else 0);
    assert sum_helper(numbers, p, 0) - sum_helper(numbers, p, i+1) == sum_helper(numbers, p, 0) - (sum_helper(numbers, p, i) - (if p[i] then numbers[i] else 0));
    i := i + 1;
  }
  assert i == |numbers|;
  assert sum_helper(numbers, p, i) == 0;
  sum_lemma(numbers, p, 0);
}
// </vc-code>
