// <vc-preamble>
function CountBoolean(s: seq<bool>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountBoolean(s[..|s|-1]) + if s[|s|-1] then
            1
        else
            0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove recursive count property */
lemma CountBooleanAppend(s: seq<bool>, b: bool)
    ensures CountBoolean(s + [b]) == CountBoolean(s) + if b then 1 else 0
{
    if |s| == 0 {
        assert s + [b] == [b];
        assert CountBoolean([b]) == if b then 1 else 0;
    } else {
        assert (s + [b])[..|s + [b]| - 1] == s;
        assert (s + [b])[|s + [b]| - 1] == b;
    }
}
// </vc-helpers>

// <vc-spec>
method CountTrue(arr: array<bool>) returns (count: int)
    ensures 0 <= count <= arr.Length
    ensures CountBoolean(arr[..]) == count
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed invariant bounds and added lemma call */
{
  count := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= count <= i
    invariant count == CountBoolean(arr[..i])
  {
    if arr[i] {
      count := count + 1;
    }
    CountBooleanAppend(arr[..i], arr[i]);
    assert arr[..i+1] == arr[..i] + [arr[i]];
    i := i + 1;
  }
  assert i == arr.Length;
  assert arr[..] == arr[..arr.Length];
}
// </vc-code>
