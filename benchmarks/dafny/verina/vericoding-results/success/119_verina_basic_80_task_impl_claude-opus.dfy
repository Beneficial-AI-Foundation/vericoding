// <vc-preamble>
function CountOccurrences(a: seq<int>, key: int): nat
{
    |set i | 0 <= i < |a| && a[i] == key|
}
// </vc-preamble>

// <vc-helpers>
function CountInRange(a: seq<int>, key: int, start: int, end: int): nat
  requires 0 <= start <= end <= |a|
{
  |set i | start <= i < end && a[i] == key|
}

/* helper modified by LLM (iteration 2): Added lemma to prove loop invariant maintenance */
lemma CountInRangeExtend(a: seq<int>, key: int, start: int, end: int)
  requires 0 <= start <= end < |a|
  ensures CountInRange(a, key, start, end + 1) == CountInRange(a, key, start, end) + (if a[end] == key then 1 else 0)
{
  var s1 := set i | start <= i < end && a[i] == key;
  var s2 := set i | start <= i < end + 1 && a[i] == key;
  if a[end] == key {
    assert s2 == s1 + {end};
  } else {
    assert s2 == s1;
  }
}

lemma CountSplit(a: seq<int>, key: int, mid: int)
  requires 0 <= mid <= |a|
  ensures CountOccurrences(a, key) == CountInRange(a, key, 0, mid) + CountInRange(a, key, mid, |a|)
{
  var left := set i | 0 <= i < mid && a[i] == key;
  var right := set i | mid <= i < |a| && a[i] == key;
  var total := set i | 0 <= i < |a| && a[i] == key;
  assert total == left + right;
  assert left * right == {};
}
// </vc-helpers>

// <vc-spec>
method OnlyOnce(a: array<int>, key: int) returns (result: bool)
    ensures result <==> CountOccurrences(a[..], key) == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariant maintenance using helper lemma */
  var count := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant count == CountInRange(a[..], key, 0, i)
  {
    var oldCount := count;
    if a[i] == key {
      count := count + 1;
    }
    CountInRangeExtend(a[..], key, 0, i);
    i := i + 1;
  }
  
  assert i == a.Length;
  assert count == CountInRange(a[..], key, 0, a.Length);
  assert CountInRange(a[..], key, 0, a.Length) == CountOccurrences(a[..], key);
  
  result := count == 1;
}
// </vc-code>
