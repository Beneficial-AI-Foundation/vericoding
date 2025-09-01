

// <vc-helpers>
/**
 * `intersperse_spec` helper lemma proves properties about the resulting sequence
 * from intersperse, which are used to verify the post-conditions.
 */
lemma intersperse_spec(numbers: seq<int>, delimeter: int, res: seq<int>)
  requires |numbers| != 0
  requires forall i :: 0 <= i < |numbers| ==>
    (forall k :: 0 <= k < i ==> 2*k+1 < |res| && res[2*k] == numbers[k] && res[2*k+1] == delimeter)
    && (2*i < |res| && res[2*i] == numbers[i])
  ensures forall i : int :: 0 <= i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  ensures forall i : int :: 0 <= i < |res| && i % 2 == 1 ==> res[i] == delimeter
{
  forall i | 0 <= i < |res| && i % 2 == 0
    ensures res[i] == numbers[i / 2]
  {
    var k := i / 2;
    if k == 0 {
      assert 0 < |numbers|; // From requires |numbers| != 0
      assert res[0] == numbers[0];
    } else {
      assert 2*k+1 < |res|; // From requires clause of lemma
      assert forall k' :: 0 <= k' < k ==> 2*k'+1 < |res| && res[2*k'] == numbers[k'] && res[2*k'+1] == delimeter;
      assert res[2*k] == numbers[k];
    }
  }

  forall i | 0 <= i < |res| && i % 2 == 1
    ensures res[i] == delimeter
  {
    var k := (i - 1) / 2;
    if k == 0 {
      assert 1 < |res|; // from pre-condition: 2*0+1 < |res|
      assert res[1] == delimeter;
    } else {
      assert 2*k+1 < |res|; // From requires clause of lemma
      assert forall k' :: 0 <= k' < k ==> 2*k'+1 < |res| && res[2*k'] == numbers[k'] && res[2*k'+1] == delimeter;
      assert res[2 * k + 1] == delimeter;
    }
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
    invariant |res_seq| == i * 2 || (|res_seq| == (i * 2) - 1 && i == |numbers|)
    invariant forall k :: 0 <= k < i ==> 2*k+1 < |res_seq| && res_seq[2*k] == numbers[k] && res_seq[2*k+1] == delimeter
    invariant i == |numbers| ==> (
      if |numbers| == 0 then
        |res_seq| == 0
      else
        |res_seq| == |numbers| * 2 - 1
    )
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

