

// <vc-helpers>
lemma EvenOddAlternating(res: seq<int>, numbers: seq<int>, delimeter: int)
  requires |numbers| != 0 ==> |numbers| * 2 - 1 == |res|
  requires |numbers| == 0 ==> |res| == 0
  requires forall i :: 0 <= i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  requires forall i :: 0 <= i < |res| && i % 2 == 1 ==> res[i] == delimeter
  ensures forall i :: 0 <= i < |res| ==> (i % 2 == 0 ==> res[i] == numbers[i / 2]) && (i % 2 == 1 ==> res[i] == delimeter)
{
}

lemma EvenIndexProperties(n: int, len: int)
  requires 0 <= n < len * 2 - 1
  ensures n % 2 == 0 ==> n / 2 < len
{
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
    res := [];
  } else {
    var i := 0;
    res := [];
    while i < |numbers| * 2 - 1
      invariant |res| == i
      invariant i % 2 == 0
      invariant forall j :: 0 <= j < i && j % 2 == 0 ==> res[j] == numbers[j / 2]
      invariant forall j :: 0 <= j < i && j % 2 == 1 ==> res[j] == delimeter
    {
      if i % 2 == 0 {
        res := res + [numbers[i / 2]];
      } else {
        res := res + [delimeter];
      }
      i := i + 1;
    }
    EvenOddAlternating(res, numbers, delimeter);
  }
}
// </vc-code>

