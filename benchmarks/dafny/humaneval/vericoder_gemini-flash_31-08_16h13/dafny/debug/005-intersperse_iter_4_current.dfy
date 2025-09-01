

// <vc-helpers>
/**
 * `intersperse_spec` helper lemma proves properties about the resulting sequence
 * from intersperse, which are used to verify the post-conditions.
 */
lemma intersperse_spec(numbers: seq<int>, delimeter: int, res: seq<int>)
  requires |numbers| != 0
  requires forall k :: 0 <= k < |numbers| - 1 ==> 2*k+1 < |res| && res[2*k] == numbers[k] && res[2*k+1] == delimeter
  requires 2*(|numbers|-1) < |res| && res[2*(|numbers|-1)] == numbers[|numbers|-1] // for the last number
  ensures forall i : int :: 0 <= i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  ensures forall i : int :: 0 <= i < |res| && i % 2 == 1 ==> res[i] == delimeter
{
  forall i | 0 <= i < |res| && i % 2 == 0
    ensures res[i] == numbers[i / 2]
  {
    var k := i / 2;
    if k < |numbers| - 1 {
      assert 2*k+1 < |res|; // From requires clause of lemma
      assert res[2*k] == numbers[k];
    } else { // k == |numbers| - 1
      assert 2*(|numbers|-1) < |res|; // From requires clause of lemma
      assert res[2*(|numbers|-1)] == numbers[|numbers|-1];
    }
  }

  forall i | 0 <= i < |res| && i % 2 == 1
    ensures res[i] == delimeter
  {
    var k := (i - 1) / 2;
    assert 2*k+1 < |res|; // From requires clause of lemma
    assert res[2*k+1] == delimeter;
  }
}
// </vc-helpers>

// <vc-spec>
method intersperse(numbers: seq<int>, delimeter: int) returns (res: seq<int>)
  // post-conditions-start
  ensures |numbers| != 0 ==> |numbers| * 2 - 1 == |res|
  ensures |numbers| == 0 ==> |res| == 0
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 1 ==> res[i] == delimeter
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |numbers| == 0 {
    return [];
  }

  var res_seq: seq<int> := [];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant i == 0 ==> |res_seq| == 0
    invariant i > 0 && i < |numbers| ==> |res_seq| == (2 * i - 1)
    invariant i == |numbers| ==> |res_seq| == (2 * |numbers| - 1)
    invariant forall k :: 0 <= k < i - 1 ==> 2*k+1 < |res_seq| && res_seq[2*k] == numbers[k] && res_seq[2*k+1] == delimeter
    invariant forall k :: 0 <= k < i && k == i-1 ==> res_seq[2*k] == numbers[k]
  {
    res_seq := res_seq + [numbers[i]];
    if i < |numbers| - 1 {
      res_seq := res_seq + [delimeter];
    }
    i := i + 1;
  }

  intersperse_spec(numbers, delimeter, res_seq);
  return res_seq;
}
// </vc-code>

